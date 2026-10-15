#!/usr/bin/env python3
"""Compile actual CREATE2 semantics mutations; unchanged regressions must reject all."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    job = parser.parse_args().output.resolve()
    job.mkdir(parents=True, exist_ok=False)
    root = Path(__file__).resolve().parents[1]
    source = root/'EvmYul/EVM/Semantics.lean'
    fixture = root/'Conform/Create2OsakaChecks.lean'
    files = [source, fixture, Path(__file__).resolve(), root/'lake-manifest.json']
    identity = {str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    body = source.read_text()
    assert body.count('namespace EVM\n')==body.count('end EVM\n')==1
    body = body.replace('namespace EVM\n','namespace Create2OsakaMutation\nopen EVM\nabbrev State := EVM.State\nabbrev ExecutionResult := EVM.ExecutionResult\n')
    body = body.replace('end EVM\n','end Create2OsakaMutation\n')
    runtime = '\nnamespace '+fixture.read_text().split('\nnamespace ',1)[1]
    runtime = runtime.replace('EVM.X','Create2OsakaMutation.X').replace('EVM.D_J','Create2OsakaMutation.D_J')
    cases = [
        ('reinstate-storage-collision','      existentAccount.nonce ≠ ⟨0⟩',
         '      existentAccount.storage != default || existentAccount.nonce ≠ ⟨0⟩'),
        ('omit-storage-reset','        storage := default\n',''),
        ('omit-nonce-collision','      existentAccount.nonce ≠ ⟨0⟩','      false'),
        ('omit-code-collision','        || existentAccount.code.size ≠ 0','        || false'),
    ]
    cmd = ['lake','env','lean',
           '--load-dynlib='+str(root/'.lake/build/lib/libleanffi.so'),
           '--load-dynlib='+str(root/'.lake/build/lib/lean/evmyul_EvmYul_FFI_ffi.so'), '--run']
    def run(name, implementation):
        path = job/(name+'.lean')
        path.write_text(implementation+runtime)
        result = subprocess.run(cmd+[str(path)],cwd=root,text=True,capture_output=True,timeout=180)
        (job/(name+'.log')).write_text(result.stdout+result.stderr)
        return result
    baseline = run('baseline',body)
    assert baseline.returncode==0 and [line for line in baseline.stdout.splitlines() if line.startswith('Osaka CREATE2')]==[
        'Osaka CREATE2 storage reset and nonce/code collision checks passed:4'],baseline.stdout+baseline.stderr
    rows=[]
    for name, old, new in cases:
        assert body.count(old)==1,name
        mutant=body.replace(old,new,1)
        result=run(name,mutant)
        replay=run(name+'-replay',mutant)
        # Compilation/loader failures do not count: the unchanged IO assertion
        # must execute and throw its specific semantic regression diagnostic.
        errors=[line for line in (result.stdout+result.stderr).splitlines()
                if line.startswith('uncaught exception: Osaka CREATE2')]
        replay_errors=[line for line in (replay.stdout+replay.stderr).splitlines()
                       if line.startswith('uncaught exception: Osaka CREATE2')]
        assert result.returncode!=0 and replay.returncode!=0
        assert len(errors)==1 and errors==replay_errors,(name,result.stdout,result.stderr)
        rows.append(dict(name=name,exit=result.returncode,detected=errors,replay=replay_errors))
    assert all(hashlib.sha256((root/p).read_bytes()).hexdigest()==h for p,h in identity.items())
    (job/'success.json').write_text(json.dumps(dict(exit=0,identity=identity,rows=rows),indent=2)+'\n')
    print('Actual CREATE2 semantics mutants detected and replayed:4')


if __name__=='__main__':
    main()

#!/usr/bin/env python3
"""Run the native CREATE2 regression, rejecting startup panics even on exit zero."""
import argparse
import hashlib
from importlib.metadata import version
import json
from pathlib import Path
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    job = parser.parse_args().output.resolve()
    job.mkdir(parents=True, exist_ok=False)
    root = Path(__file__).resolve().parents[1]
    binary = root/'.lake/build/bin/create2OsakaChecks'
    files = [root/'EvmYul/EVM/Semantics.lean', root/'Conform/Create2OsakaChecks.lean',
             Path(__file__).resolve(), root/'requirements-native-tests.txt', binary]
    identity = {str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    packages = {name:version(name) for name in
                ['coincurve','typing-extensions','pycryptodome','eth-typing','py-ecc']}
    result = subprocess.run([str(binary)], cwd=root, text=True, capture_output=True, timeout=180)
    (job/'runtime.log').write_text(result.stdout+result.stderr)
    # unsafePerformIO panics during module initialization can leave exit status
    # zero. They must never be mistaken for a successful native regression.
    assert result.returncode==0, result.stdout+result.stderr
    assert not result.stderr, result.stderr
    assert result.stdout.splitlines()==[
        'Osaka CREATE2 storage reset and nonce/code collision checks passed:4'], result.stdout
    assert all(hashlib.sha256((root/p).read_bytes()).hexdigest()==h for p,h in identity.items())
    (job/'success.json').write_text(json.dumps(dict(exit=0,identity=identity,packages=packages,
        python=sys.version,output=result.stdout.splitlines()),indent=2)+'\n')
    print('Clean native Osaka CREATE2 regression passed:4')


if __name__=='__main__':
    main()

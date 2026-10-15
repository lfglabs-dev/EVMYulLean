#!/usr/bin/env python3
"""Capture four CREATE2 target-account cases on Foundry Osaka (anvil/cast on PATH)."""
import argparse
import hashlib
import json
from pathlib import Path
import socket
import subprocess
import time
from urllib.error import URLError
from urllib.request import Request, urlopen


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    job = parser.parse_args().output.resolve()
    job.mkdir(parents=True, exist_ok=False)
    root = Path(__file__).resolve().parents[1]
    files = [Path(__file__).resolve(), root/'EvmYul/EVM/Semantics.lean', root/'Conform/Create2OsakaChecks.lean']
    identity = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    with socket.socket() as sock:
        sock.bind(('127.0.0.1', 0))
        port = sock.getsockname()[1]
    url = f'http://127.0.0.1:{port}'
    counter = 0
    def rpc(method, *params):
        nonlocal counter
        counter += 1
        request = Request(url, json.dumps(dict(jsonrpc='2.0', id=counter, method=method, params=list(params))).encode(),
                          {'Content-Type':'application/json'})
        with urlopen(request, timeout=30) as response:
            result = json.load(response)
        if 'error' in result or result.get('id') != counter:
            raise RuntimeError(f'RPC {method} failed: {result}')
        return result['result']
    creator = '0x'+format(8193,'040x')
    header = bytes.fromhex('600b380380600b5f395ff3')
    code = bytes.fromhex('6063600755') + b'\x7f' + header.ljust(32,b'\0') + bytes.fromhex('5f526007600b5f5ff55f5260205ff3')
    hash_code = subprocess.check_output(['cast','keccak','0x'+header.hex()],text=True).strip()
    target = '0x'+subprocess.check_output(['cast','keccak','0xff'+creator[2:]+format(7,'064x')+hash_code[2:]],text=True).strip()[-40:]
    assert target == '0xe317ec6689ba1293927261f8acda33b2db0bb1ba'
    args = ['anvil','--host','127.0.0.1','--port',str(port),'--hardfork','osaka',
            '--timestamp','1000000000','--chain-id','31337','--steps-tracing','--quiet']
    versions = {name:subprocess.check_output([name,'--version'],text=True).strip() for name in ['anvil','cast']}
    with (job/'anvil.log').open('w') as log:
        proc = subprocess.Popen(args, stdout=log, stderr=subprocess.STDOUT)
        try:
            deadline = time.monotonic()+10
            while True:
                if proc.poll() is not None or time.monotonic() > deadline:
                    raise RuntimeError('owned Anvil failed to start')
                try:
                    assert rpc('eth_chainId') == '0x7a69'
                    break
                except (URLError, TimeoutError):
                    time.sleep(.05)
            sender = rpc('eth_accounts')[0]
            rows = []
            for name, nonce, target_code, slot, created in [
                ('storage-only',0,'0x',77,True), ('balance-only',0,'0x',0,True),
                ('nonce-collision',1,'0x',77,False), ('code-collision',0,'0x00',77,False)]:
                snapshot = rpc('evm_snapshot')
                rpc('anvil_setCode',creator,'0x'+code.hex())
                rpc('anvil_setStorageAt',creator,hex(7),'0x'+format(23,'064x'))
                rpc('anvil_setCode',target,target_code)
                rpc('anvil_setNonce',target,hex(nonce))
                rpc('anvil_setBalance',target,hex(19))
                rpc('anvil_setStorageAt',target,hex(9),'0x'+format(slot,'064x'))
                initial = dict(nonce=rpc('eth_getTransactionCount',target,'latest'),
                    code=rpc('eth_getCode',target,'latest'),balance=rpc('eth_getBalance',target,'latest'),
                    slot9=rpc('eth_getStorageAt',target,hex(9),'latest'))
                assert int(initial['slot9'],16)==slot and int(initial['nonce'],16)==nonce
                txhash = rpc('eth_sendTransaction',{'from':sender,'to':creator,'data':'0x','gas':hex(1021000)})
                receipt = None
                deadline = time.monotonic()+10
                while receipt is None and time.monotonic()<deadline:
                    receipt = rpc('eth_getTransactionReceipt',txhash)
                    if receipt is None:
                        time.sleep(.02)
                assert receipt is not None and receipt['status']=='0x1' and receipt['logs']==[]
                call = rpc('debug_traceTransaction',txhash,{'tracer':'callTracer'})
                trace = rpc('debug_traceTransaction',txhash,{'enableMemory':True})
                idx, entry = next((i,r) for i,r in enumerate(trace['structLogs']) if r['op']=='CREATE2')
                after = next(r for r in trace['structLogs'][idx+1:] if r['depth']==entry['depth'])
                assert int(call.get('output','0x'),16) == (int(target,16) if created else 0)
                final = dict(nonce=rpc('eth_getTransactionCount',target,'latest'),
                    code=rpc('eth_getCode',target,'latest'),balance=rpc('eth_getBalance',target,'latest'),
                    slot9=rpc('eth_getStorageAt',target,hex(9),'latest'),
                    creatorNonce=rpc('eth_getTransactionCount',creator,'latest'),
                    creatorSlot7=rpc('eth_getStorageAt',creator,hex(7),'latest'))
                assert int(final['nonce'],16)==(1 if created else nonce)
                assert final['code']==('0x' if created else target_code)
                assert int(final['balance'],16)==19
                assert int(final['slot9'],16)==(0 if created else slot)
                assert int(final['creatorNonce'],16)==1 and int(final['creatorSlot7'],16)==99
                (job/(name+'-trace.json')).write_text(json.dumps(trace,indent=2)+'\n')
                rows.append(dict(name=name,initial=initial,final=final,receipt=receipt,call=call,entry=entry,afterCreate=after))
                assert rpc('evm_revert',snapshot)
        finally:
            if proc.poll() is None:
                proc.terminate()
                try:
                    proc.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    proc.kill()
                    proc.wait(timeout=5)
    assert all(hashlib.sha256((root/p).read_bytes()).hexdigest()==h for p,h in identity.items())
    (job/'success.json').write_text(json.dumps(dict(exit=0,identity=identity,versions=versions,
        arguments=args,creator=creator,target=target,code=code.hex(),rows=rows),indent=2)+'\n')
    print('Real EVM Osaka CREATE2 target cases passed:4')


if __name__ == '__main__':
    main()

from pathlib import Path
import json
D=Path(__file__).resolve().parents[1]
def push2(x):
    assert 0<=x<65536
    return b'\x61'+x.to_bytes(2,'big')
records=[]
for tag in ['stock','M1','M2','M3']:
    original=bytes.fromhex((D/f'runtime/{tag}.hex').read_text().strip()[2:])
    for mode,start,stop,words in [('loop',1964,2170,9),('post',2170,369,8)]:
        code=bytearray(original)
        entry=len(code)
        init=b'\x5b\x60\x80\x60\x40\x52' # JUMPDEST; mstore(64,128)
        for i in reversed(range(words)):
            init+=push2(32*i)+b'\x35'
        init+=push2(start)+b'\x56'
        capture=entry+len(init)
        count=words if mode=='loop' else 1
        finish=b'\x5b'
        for i in range(count):
            finish+=push2(32*i)+b'\x52' # capture the original stack, top first
        finish+=push2(32*count)+b'\x5f\xf3'
        code+=init+finish
        code[0:4]=push2(entry)+b'\x56'
        assert original[start]==original[stop]==0x5b
        code[stop:stop+5]=b'\x5b'+push2(capture)+b'\x56'
        changed=[i for i,(a,b) in enumerate(zip(original,code)) if a!=b]
        assert all(i in range(4) or i in range(stop,stop+5) for i in changed)
        if mode=='loop': assert code[start:stop]==original[start:stop]
        else: assert code[start:2228]==original[start:2228]
        (D/f'runtime/{tag}-{mode}.hex').write_text('0x'+code.hex())
        records.append(dict(tag=tag,mode=mode,entry=start,exit=stop,appended_entry=entry,appended_capture=capture,changed_original_offsets=changed,stack_words=words,returned_words=count))
(D/'runtime/instrumentation.json').write_text(json.dumps(records,indent=2)+'\n')
print('Verified boundary-only instrumentation for all eight runtime variants.')

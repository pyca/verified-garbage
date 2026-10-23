"""Build temporary fixtures from pinned published C2SP Wycheproof vectors."""
import hashlib
import json
from pathlib import Path
from urllib.request import urlopen

url = 'https://raw.githubusercontent.com/C2SP/wycheproof/a3d5d1423f2592d6646836a45a21a1b209da9f4d/testvectors_v1/ed448_test.json'
data = json.load(urlopen(url))
order = 2**446 - 13818066809895115352007386748515426880336692474882178609894547503885
rows = []
def array(value):
    return '{' + ','.join(map(str, value)) + '}'
for group in data['testGroups']:
    public = bytes.fromhex(group['publicKey']['pk'])
    for test in group['tests']:
        signature = bytes.fromhex(test['sig'])
        if len(signature) != 114:
            continue
        message = bytes.fromhex(test['msg'])
        digest = hashlib.shake_256(b'SigEd448\0\0' + signature[:57] + public + message).digest(114)
        challenge = (int.from_bytes(digest, 'little') % order).to_bytes(57, 'little')
        rows.append('{' + ','.join([str(test['tcId']), str(int(test['result'] == 'valid')), array(public), array(signature), array(challenge)]) + '}')
Path('/tmp/vg-ed448-arm64/cases.h').write_text('struct sample {int id,valid; unsigned char pk[57],sig[114],k[57];};\nstatic const struct sample samples[]={\n' + ',\n'.join(rows) + '\n};\n')
print(len(rows), 'published fixed-length cases')

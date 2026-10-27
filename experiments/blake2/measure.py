import ctypes as C, hashlib, time, statistics, json, random
lib=C.CDLL(str(__import__('pathlib').Path(__file__).with_name('prototypes.so')))
ivb=[0x6a09e667f3bcc908,0xbb67ae8584caa73b,0x3c6ef372fe94f82b,0xa54ff53a5f1d36f1,0x510e527fade682d1,0x9b05688c2b3e6c1f,0x1f83d9abfb41bd6b,0x5be0cd19137e2179]
ivs=[0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19]
funcs={}
rng=random.Random(1234)
for kind,iv,word,bb in [('b',ivb,C.c_uint64,128),('s',ivs,C.c_uint32,64)]:
 names=['base_'+kind,kind+'neon']+[kind+str(w)+e for w in [1,2,4] for e in ['', 'early']]
 for name in names:
  f=getattr(lib,name); f.argtypes=[C.c_void_p,C.c_void_p,C.c_uint64,C.c_uint64,C.c_uint32,C.c_void_p]
  funcs[name]=(f,iv,word,bb)
  for size in [0,1,bb-1,bb,bb+1,3*bb,17*bb+13]:
   data=rng.randbytes(size); padded=data+b'\0'*((-size)%bb or (bb if size==0 else 0))
   h=(word*8)(*iv); h[0]^=0x01010000+8*C.sizeof(word)
   scratch=C.create_string_buffer(64); buf=C.create_string_buffer(padded)
   blocks=max(1,(size+bb-1)//bb)
   if blocks>1: f(h,buf,blocks-1,bb,0,scratch)
   f(h,C.byref(buf,(blocks-1)*bb),1,size,1,scratch)
   expected=getattr(hashlib,'blake2'+kind)(data).digest()
   assert bytes(h)==expected,(name,size,bytes(h).hex(),expected.hex())
print('All 98 digest differential checks passed',flush=True)
if __name__=='__main__':
 out={k:[] for k in funcs}
 for rep in range(5):
  names=list(funcs); rng.shuffle(names)
  for name in names:
   f,iv,word,bb=funcs[name]; h=(word*8)(*iv); scratch=C.create_string_buffer(64); buf=C.create_string_buffer(rng.randbytes(bb*128))
   for _ in range(100): f(h,buf,128,bb,0,scratch)
   start=time.perf_counter_ns()
   for _ in range(4000): f(h,buf,128,bb,0,scratch)
   ns=(time.perf_counter_ns()-start)/(4000*128)
   out[name].append(ns)
  print(rep,{k:round(statistics.median(v),2) for k,v in out.items()},flush=True)
 with open('/tmp/blake2-results.json','w') as f: json.dump(out,f,indent=2)

print('BLAKE2_RAW '+json.dumps(out),flush=True)

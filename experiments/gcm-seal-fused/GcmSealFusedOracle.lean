import VerifiedGarbage.Spec.Gcm
open VG

def pushBytes (a : ByteArray) (bs : List Byte) : ByteArray :=
 bs.foldl (fun a b => a.push b.toNat.toUInt8) a

def next (s : BitVec 128) := s * 0x2360ed051fc65da44385df649fccf645 + 0x14057b7ef767814f

def main : IO Unit := do
 let mut input := ByteArray.empty
 let mut expected := ByteArray.empty
 let mut seed : BitVec 128 := 0x123456789abcdef
 let sizes := [0,1,15,16,17,47,63,127,128,129,511,512,513,1023,1024,1025,16384,16385]
 for trial in [:54] do
  let n := sizes[trial % sizes.length]!
  let keyLen := [16,24,32][trial / sizes.length]!
  let nonceLen := [1,8,12,13,16,31][trial % 6]!
  let aadLen := [0,1,13,16,17,63][trial % 6]!
  let mut key : List Byte := []
  for _ in [:keyLen] do
   seed := next seed
   key := key ++ [seed.extractLsb' 0 8]
  let nr := Spec.Aes.rounds (keyLen/4)
  let w := Spec.Aes.expandKey key
  let cipher := Spec.Gcm.aesWith nr w
  let h := cipher 0
  let mut iv : List Byte := []
  let mut aad : List Byte := []
  let mut text : List Byte := []
  for _ in [:nonceLen] do
   seed := next seed
   iv := iv ++ [seed.extractLsb' 0 8]
  for _ in [:aadLen] do
   seed := next seed
   aad := aad ++ [seed.extractLsb' 0 8]
  for i in [:n] do text := text ++ [BitVec.ofNat 8 (17*i+trial)]
  for x in [nr,nonceLen,aadLen,n] do
   for j in [:8] do input := input.push ((x >>> (8*j)) % 256).toUInt8
  input := pushBytes input (w ++ List.replicate (240-w.length) 0 ++ Spec.Gcm.toBytes h)
  input := pushBytes input (iv ++ aad ++ text)
  let (ct,tag) := Spec.Gcm.encryptWith cipher h 16 iv text aad
  for _ in [:2] do expected := pushBytes expected (ct ++ tag)
 IO.FS.writeBinFile "/workspace/scratch/gcm-seal-fused-input.bin" input
 IO.FS.writeBinFile "/workspace/scratch/gcm-seal-fused-expected.bin" expected
 IO.println s!"54 full-seal Spec cases x 2 variants; {expected.size} expected bytes"

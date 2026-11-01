import VerifiedGarbage.Spec.Gcm
open VG

def pushBytes (a : ByteArray) (bs : List Byte) : ByteArray :=
 bs.foldl (fun a b => a.push b.toNat.toUInt8) a

def pushBlock (a : ByteArray) (b : BitVec 128) := pushBytes a (Spec.Gcm.toBytes b)
def next (s : BitVec 128) := s * 0x2360ed051fc65da44385df649fccf645 + 0x14057b7ef767814f

def main : IO Unit := do
 let mut input := ByteArray.empty
 let mut expected := ByteArray.empty
 let mut seed : BitVec 128 := 0x123456789abcdef
 for trial in [:18] do
  let n := [0,24,48,72,96,120][trial % 6]!
  let keyLen := [16,24,32][trial / 6]!
  let mut key : List Byte := []
  for _ in [:keyLen] do
   seed := next seed
   key := key ++ [seed.extractLsb' 0 8]
  let nr := Spec.Aes.rounds (keyLen/4)
  let w := Spec.Aes.expandKey key
  seed := next seed
  let cb := if trial % 2 = 0 then seed.extractLsb' 32 96 ++ (0xfffffffc : BitVec 32) else seed
  seed := next seed
  let h := seed
  seed := next seed
  let y := seed
  let mut blocks : List (BitVec 128) := []
  for _ in [:n] do
   seed := next seed
   blocks := blocks ++ [seed]
  for x in [n,nr] do
   for j in [:8] do input := input.push ((x >>> (8*j)) % 256).toUInt8
  input := pushBytes input (w ++ List.replicate (240-w.length) 0)
  for b in [cb,h,y] ++ blocks do input := pushBlock input b
  let ciphertext := Spec.Gcm.ctr32 (Spec.Gcm.aesWith nr w) cb blocks
  for _ in [:5] do
   expected := pushBlock expected (Nat.repeat Spec.Gcm.inc32 n cb)
   expected := pushBlock expected (Spec.Gcm.ghashFrom h y ciphertext)
   for b in ciphertext do expected := pushBlock expected b
 IO.FS.writeBinFile "/workspace/scratch/gcm-fused-input.bin" input
 IO.FS.writeBinFile "/workspace/scratch/gcm-fused-expected.bin" expected
 IO.println s!"18 spec cases, five variants, {expected.size} expected bytes"

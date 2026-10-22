module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.Chain

/-! # Fixed-exponent chains using the existing field multiplication calls -/

@[expose] public section
namespace VG.Impl.EcKey.Compressed.AArch64.Chain
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

 def mul (P : ChainCfg) (o a b : Nat) : Prog isa :=
  match Mont.callOf P.M with
  | some (f, m) => mulCall f P.M.n m o a b
  | none => .block (Mont.AArch64.mul P.M o a b)

 def oddPowers (P : ChainCfg) : Nat → Prog isa
  | 0 => .block []
  | k + 1 => .seq (oddPowers P k) (mul P (P.slot (k + 1)) (P.slot k) (P.slot 8))

 def table (P : ChainCfg) : Prog isa :=
  .seq (.block (copy P.M.n (P.slot 0) P.base))
    (.seq (mul P (P.slot 8) P.base P.base) (oddPowers P 7))

 def squares (P : ChainCfg) (k : Nat) : Prog isa :=
  .seq (.block [.movz .x .x19 (BitVec.ofNat 16 k) 0])
    (.loop (.seq (.block [decCounter]) (mul P P.acc P.acc P.acc)) (.nonzero .x .x19))

 def step (P : ChainCfg) : Nat × Nat → Prog isa
  | (k, d) => .seq (if k = 0 then .block [] else squares P k)
    (if d = 0 then .block [] else mul P P.acc P.acc (P.slot ((d - 1) / 2)))

 def steps (P : ChainCfg) : List (Nat × Nat) → Prog isa
  | [] => .block []
  | st :: rest => .seq (step P st) (steps P rest)

 def pow (P : ChainCfg) : Prog isa :=
  .seq (table P) (.seq (.block (copy P.M.n P.acc (P.slot ((P.first - 1) / 2)))) (steps P P.steps))

end VG.Impl.EcKey.Compressed.AArch64.Chain

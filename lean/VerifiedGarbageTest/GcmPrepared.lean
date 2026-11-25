module

import VerifiedGarbage.Spec.Gcm.Prepared
meta import VerifiedGarbage.Spec.Gcm.Prepared
import VerifiedGarbage.Impl.Gcm.X86_64.StitchZP
meta import VerifiedGarbage.Impl.Gcm.X86_64.StitchZP

/-!
Check the prepared storage encoding against the existing instruction-model
conversion. These are representation tests, not cryptographic known-answer
vectors: inputs are the zero word, all ones and every single-bit word.
-/

namespace VG.Test.GcmPrepared
open VG.X86_64 VG.Spec.Gcm
open VG.Impl.Gcm.X86_64

def inputs : List Block := ([0, -1] : List Block) ++ (List.range 128).map (fun i => (1 : Block) <<< i)

def convert (odd even : Block) : Option State :=
  let s : State := {
    gpr := fun r => if r = .rdi then 0x1000 else 0
    cf := none
    zf := none
    sf := none
    of := none
    mem := fun a =>
      if a.toNat < 0x1110 then odd.extractLsb' (8 * (15 - (a.toNat - 0x1100))) 8
      else even.extractLsb' (8 * (15 - (a.toNat - 0x1110))) 8
    rd := [⟨0x1100, 32⟩]
    wr := [] }
  let code := Pclmul.const .xmm0 Pclmul.revMask ++ Pclmul.const .xmm1 Pclmul.poly ++
    ([.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1),
      .vop (.vinserti128 .xmm1 .xmm1 .xmm1 1)] : List Instr) ++
    StitchZP.cvtConsts ++ StitchZP.cvtPair 1 .xmm3
  code.foldlM (fun t i => exec i t) s

-- Distinct adjacent powers catch lane swaps as well as byte-order mistakes.
#guard inputs.all fun v =>
  match convert v (~~~v) with
  | none => false
  | some s => s.xmm .xmm3 == preparedPower (~~~v) &&
      s.ymmHi .xmm3 == preparedPower v

-- Build a complete raw-power context, convert it in place with the existing
-- instructions, then check the new representation predicate itself.
def h : Block := (List.range 16).foldl (fun v i => (v <<< 8) ||| BitVec.ofNat 128 i) 0

def rawMem : Mem := fun a =>
  let offset := a.toNat - 0x1000
  let v := if offset < 256 then h else hpow h ((offset - 256) / 16 + 1)
  v.extractLsb' (8 * (15 - offset % 16)) 8

def prepared : Option State :=
  let s : State := {
    gpr := fun r => if r = .rdi then 0x1000 else 0
    cf := none, zf := none, sf := none, of := none
    mem := rawMem, rd := [⟨0x1000, 1024⟩], wr := [⟨0x1100, 768⟩] }
  let code := Pclmul.const .xmm0 Pclmul.revMask ++ Pclmul.const .xmm1 Pclmul.poly ++
    ([.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1),
      .vop (.vinserti128 .xmm1 .xmm1 .xmm1 1)] : List Instr) ++
    StitchZP.cvtConsts ++ (List.range 24).flatMap (fun k =>
      StitchZP.cvtPair (2*k+1) .xmm3 ++
      [.vmovdquStore .l256 (Pclmul.at_ .rdi (256+32*k)) .xmm3])
  code.foldlM (fun t i => exec i t) s

local instance (m : Mem) (p : Addr) : Decidable (PreparedPowersRepr m p) := by
  unfold PreparedPowersRepr
  infer_instance

#guard match prepared with
  | none => false
  | some s => decide (PreparedPowersRepr s.mem 0x1000) &&
      (List.range 256).all (fun i => s.mem (0x1000 + BitVec.ofNat 64 i) ==
        rawMem (0x1000 + BitVec.ofNat 64 i))
#guard !decide (PreparedPowersRepr rawMem 0x1000)

/-! ## What `prepare` writes, `wipe` zeroes (#6333)

Of the contracts alone, whatever the implementations. -/

theorem bytesAt_byte {m m' : Mem} {p : Addr} {n : Nat} (h : Spec.Aes.bytesAt m p n = Spec.Aes.bytesAt m' p n)
    {i : Nat} (hi : i < n) : m (p + BitVec.ofNat 64 i) = m' (p + BitVec.ofNat 64 i) := by
  have := congrArg (·[i]?) h
  simpa only [Spec.Aes.bytesAt, List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.some.injEq]
    using this

/-- After `prepare` (from `m` to `m'`) and `wipe` (to `m''`), each byte of the
context but its count is zero, or was never written. -/
theorem prepare_wipe {pb : Nat} {ctx : Addr} {m m' m'' : Mem} {r r'} (hp : preparePost pb ctx m m' r)
    (hw : wipePreparedPost pb ctx m' m'' r') (i : Nat) (hi : i < 1024) :
    m'' (ctx + BitVec.ofNat 64 i) = 0 ∨
      256 ≤ i ∧ m'' (ctx + BitVec.ofNat 64 i) = m (ctx + BitVec.ofNat 64 i) := by
  obtain ⟨-, -, -, keep⟩ := hp
  obtain ⟨zero, rest⟩ := hw
  have hl : 256 ≤ wipePreparedLen m' ctx ∧ wipePreparedLen m' ctx ≤ 1024 := by
    unfold wipePreparedLen; split
    · decide
    · split <;> decide
  by_cases h : i < wipePreparedLen m' ctx
  · left
    have := congrArg (·[i]?) zero
    simpa only [Spec.Aes.bytesAt, List.getElem?_map, List.getElem?_range h, Option.map_some,
      List.getElem?_replicate, h, ↓reduceIte, Option.some.injEq] using this
  · right
    have e : ctx + BitVec.ofNat 64 i =
        ctx + BitVec.ofNat 64 (wipePreparedLen m' ctx) + BitVec.ofNat 64 (i - wipePreparedLen m' ctx) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, show wipePreparedLen m' ctx + (i - wipePreparedLen m' ctx) = i by omega]
    refine ⟨by omega, ?_⟩
    rw [e, bytesAt_byte rest (by omega), bytesAt_byte keep (by omega)]

/-- `prepare` may not leave the count as it finds it: the caller need not
initialize it, and any other value than 0, 16 and 48 breaks the contract. -/
example {pb : Nat} {ctx : Addr} {m m' : Mem} {r} (stale : powerCount m' ctx = powerCount m ctx)
    (h0 : powerCount m ctx ≠ 0) (h16 : powerCount m ctx ≠ 16) (h48 : powerCount m ctx ≠ 48) :
    ¬ preparePost pb ctx m m' r := by
  rintro ⟨-, -, h | h | h, -⟩ <;> omega

end VG.Test.GcmPrepared

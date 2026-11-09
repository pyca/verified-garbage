module

import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Body
public import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Entry
public import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.CTReady
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarVerified
import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Init
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseVerified
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.X25519.AArch64.Ladder
meta import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Body
meta import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Entry
meta import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.CTReady
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
meta import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarVerified
meta import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Init
meta import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseVerified
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.X25519.AArch64.Ladder
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-! # Constant time of signing after its first step (AArch64), and a witness's seed and key -/

@[expose] public section

/-! Merged from `Proof.Ed25519.AArch64.SignCached.CTBody`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.SignCached.CTHash`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole VG.Impl.Ed25519.AArch64.SignCached
variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem init_call_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L [(.x0, .caller 5 0)]))
      (.call Spec.Sha512.init512Api.name (Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512))
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL ha hb (Proof.Sha512.AArch64.Stream.init_verified _).1
    (Proof.Sha512.AArch64.Stream.init_verified _).2.1 (Whole.depth_of_noFrames rfl)
  · intro g v m t _ _ _ hs
    have h := hs (.x0, .caller 5 0) (by simp)
    change t.gpr .x0 = L.scr + 0#64 at h
    rw [BitVec.add_zero] at h
    exact init_ready h
  · intro a b ar aw br bw h
    have hsp := two_sp h
    exact ⟨call_gpr_eq (p := (.x0, .caller 5 0)) h (by simp) (by decide), hsp⟩

theorem update_call_ct (backend : Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (count : Nat) (p n : Value)
    (hi : Input L (value L p) (value L n)) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L
      [(.x0, .caller 5 0), (.x1, .const count), (.x2, p), (.x3, n), (.x4, .caller 5 192)]))
      (.call ("vg_sha512_update_scratch" ++ backend.suffix) backend.update)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL ha hb backend.update_verified.1 backend.update_verified.2.1 (Whole.update_depth backend)
  · intro g v m t hc _ _ hs
    have a0 := hs (.x0, .caller 5 0) (by simp)
    change t.gpr .x0 = L.scr + 0#64 at a0
    rw [BitVec.add_zero] at a0
    exact update_ready hL hc.sp hi ⟨a0, hs (.x1, .const count) (by simp), hs (.x2, p) (by simp),
      hs (.x3, n) (by simp), hs (.x4, .caller 5 192) (by simp)⟩
  · intro a b ar aw br bw h
    have hsp := two_sp h
    exact ⟨call_gpr_eq (p := (.x0, .caller 5 0)) h (by simp) (by decide),
      call_gpr_eq (p := (.x1, .const count)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.x2, p)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.x3, n)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.x4, .caller 5 192)) h (by simp) (by decide), hsp⟩

theorem finalize_call_ct (backend : Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (n : Nat) (b : Bool) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L
      [(.x0, .caller 5 0), (.x1, if b then .caller 4 n else .const n),
        (.x2, .frame 192), (.x3, .caller 5 192)]))
      (.call ("vg_sha512_finalize_scratch" ++ backend.suffix) backend.finalize)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL ha hb backend.finalize_verified.1 backend.finalize_verified.2.1 (Whole.finalize_depth backend)
  · intro g v m t hc _ _ hs
    have a0 := hs (.x0, .caller 5 0) (by simp)
    change t.gpr .x0 = L.scr + 0#64 at a0
    rw [BitVec.add_zero] at a0
    exact finalize_ready hL hc.sp ⟨a0, hs (.x1, if b then .caller 4 n else .const n) (by simp),
      hs (.x2, .frame 192) (by simp), hs (.x3, .caller 5 192) (by simp)⟩
  · intro a c ar aw br bw h
    have hsp := two_sp h
    exact ⟨call_gpr_eq (p := (.x0, .caller 5 0)) h (by simp) (by decide),
      call_gpr_eq (p := (.x1, if b then .caller 4 n else .const n)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.x2, .frame 192)) h (by simp) (by decide),
      call_gpr_eq (p := (.x3, .caller 5 192)) h (by simp) (by decide), hsp⟩

theorem init_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) init
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb [(.x0, .caller 5 0)] (by decide) (by decide)
    (by decide) (by taint_decide)).seq (init_call_ct hL ha hb)

theorem update_ct (backend : Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (count : Nat) (p n : Value) (hc : count < 65536) (hp : Whole.valid p) (hn : Whole.valid n)
    (hi : Input L (value L p) (value L n))
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setup
      [(.x0, .caller 5 0), (.x1, .const count), (.x2, p), (.x3, n), (.x4, .caller 5 192)])) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True)
      (update backend.code backend.suffix (setup
        [(.x0, .caller 5 0), (.x1, .const count), (.x2, p), (.x3, n), (.x4, .caller 5 192)]))
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hv : ∀ x : Reg × Value, x ∈ [(.x0, .caller 5 0), (.x1, .const count),
      (.x2, p), (.x3, n), (.x4, .caller 5 192)] → Whole.valid x.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl | rfl)
    · decide
    · exact hc
    · exact hp
    · exact hn
    · decide
  exact (setup_ct hL ha hb _ (by simp) hv (by simp [preserved]) ht).seq
    (update_call_ct backend hL ha hb count p n hi)

theorem finalize_ct (backend : Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (n : Nat) (hn : n < 4096) (b : Bool)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (finalizeArgs n b)) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (finalize backend.code backend.suffix n b)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hv : Whole.valid (if b then .caller 4 n else .const n) := by
    cases b <;> simp [Whole.valid] <;> omega
  have hvall : ∀ p : Reg × Value, p ∈ [(.x0, .caller 5 0),
      (.x1, if b then .caller 4 n else .const n), (.x2, .frame 192), (.x3, .caller 5 192)] → Whole.valid p.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl)
    · decide
    · exact hv
    · decide
    · decide
  exact (setup_ct hL ha hb _ (by simp) hvall (by simp [preserved]) ht).seq
    (finalize_call_ct backend hL ha hb n b)

end VG.Proof.Ed25519.AArch64.SignCached
end

/-! Merged from `Proof.Ed25519.AArch64.SignCached.CTHashPipeline`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole VG.Impl.Ed25519.AArch64.SignCached
variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem hashNonce_ct (backend : Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (hashNonce backend.code backend.suffix)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hp : Input L (value L (.frame 64)) (value L (.const 32)) := prefix_input hL
  have hm : Input L (value L (.caller 3 0)) (value L (.caller 4 0)) := by
    change Input L (L.msg + 0#64) (L.len + 0#64)
    rw [BitVec.add_zero, BitVec.add_zero]
    exact message_input hL
  exact (init_ct hL ha hb).seq ((update_ct backend hL ha hb 0 (.frame 64) (.const 32)
    (by decide) (by decide) (by decide) hp (by taint_decide)).seq
    ((update_ct backend hL ha hb 32 (.caller 3 0) (.caller 4 0)
      (by decide) (by decide) (by decide) hm (by taint_decide)).seq
      (finalize_ct backend hL ha hb 32 (by decide) true (by taint_decide))))

theorem hashChallenge_ct (backend : Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (hashChallenge backend.code backend.suffix)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have ho : Input L (value L (.caller 0 0)) (value L (.const 32)) := by
    change Input L (L.out + 0#64) 32#64
    rw [BitVec.add_zero]
    exact point_input hL
  have hk : Input L (value L (.caller 2 0)) (value L (.const 32)) := by
    change Input L (L.pk + 0#64) 32#64
    rw [BitVec.add_zero]
    exact key_input hL
  have hm : Input L (value L (.caller 3 0)) (value L (.caller 4 0)) := by
    change Input L (L.msg + 0#64) (L.len + 0#64)
    rw [BitVec.add_zero, BitVec.add_zero]
    exact message_input hL
  exact (init_ct hL ha hb).seq ((update_ct backend hL ha hb 0 (.caller 0 0) (.const 32)
    (by decide) (by decide) (by decide) ho (by taint_decide)).seq
    ((update_ct backend hL ha hb 32 (.caller 2 0) (.const 32)
      (by decide) (by decide) (by decide) hk (by taint_decide)).seq
      ((update_ct backend hL ha hb 64 (.caller 3 0) (.caller 4 0)
        (by decide) (by decide) (by decide) hm (by taint_decide)).seq
        (finalize_ct backend hL ha hb 64 (by decide) true (by taint_decide)))))

end VG.Proof.Ed25519.AArch64.SignCached
end

/-! Merged from `Proof.Ed25519.AArch64.SignCached.CTPrimitives`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole VG.Impl.Ed25519.AArch64.SignCached
variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem reduce_call_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) (d : Nat) (hd : d + 32 ≤ 256) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L [(.x0, .frame d), (.x1, .frame 192), (.x2, .caller 5 0)]))
      (.call "vg_ed25519_scalar_reduce" Impl.Ed25519.AArch64.scalarReduce)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL ha hb scalarReduce_ok scalarReduce_ct (Whole.depth_of_noFrames reduce_noFrames)
  · intro g v m t _ _ _ hs
    have a0 := hs (.x0, .frame d) (by simp)
    have a1 := hs (.x1, .frame 192) (by simp)
    have a2 := hs (.x2, .caller 5 0) (by simp)
    change t.gpr .x2 = L.scr + 0#64 at a2
    rw [BitVec.add_zero] at a2
    exact reduce_ready hL hd ⟨a0, a1, a2⟩
  · intro a b ar aw br bw h
    have hsp := two_sp h
    exact ⟨hsp, call_gpr_eq (p := (.x0, .frame d)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.x1, .frame 192)) h (by simp) (by decide),
      call_gpr_eq (p := (.x2, .caller 5 0)) h (by simp) (by decide)⟩

theorem base_call_ct [VG.Proof.Ed25519.AArch64.Divstep.Sound] (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L [(.x0, .caller 0 0), (.x1, .frame 96), (.x2, .caller 5 0)]))
      (.call "vg_ed25519_scalar_base" Impl.Ed25519.AArch64.scalarBase)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL ha hb scalarBase_ok scalarBase_ct (Whole.depth_of_noFrames base_noFrames)
  · intro g v m t _ _ _ hs
    have a0 := hs (.x0, .caller 0 0) (by simp)
    change t.gpr .x0 = L.out + 0#64 at a0
    rw [BitVec.add_zero] at a0
    have a1 := hs (.x1, .frame 96) (by simp)
    have a2 := hs (.x2, .caller 5 0) (by simp)
    change t.gpr .x2 = L.scr + 0#64 at a2
    rw [BitVec.add_zero] at a2
    exact base_ready hL ⟨a0, a1, a2⟩ ‹_› ‹_›
  · intro a b ar aw br bw h
    have hsp := two_sp h
    exact ⟨hsp, call_gpr_eq (p := (.x0, .caller 0 0)) h (by simp) (by decide),
      call_gpr_eq (p := (.x1, .frame 96)) h (by simp) (by decide),
      call_gpr_eq (p := (.x2, .caller 5 0)) h (by simp) (by decide),
      h.2.2.2.2.1.trans h.2.2.2.2.2.symm⟩

theorem mul_call_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L [(.x0, .caller 0 32), (.x1, .frame 96), (.x2, .frame 128), (.x3, .frame 32), (.x4, .caller 5 0)]))
      (.call "vg_ed25519_scalar_mul_add" Impl.Ed25519.AArch64.scalarMulAdd)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL ha hb scalarMulAdd_ok scalarMulAdd_ct (Whole.depth_of_noFrames mul_noFrames)
  · intro g v m t _ _ _ hs
    have a0 := hs (.x0, .caller 0 32) (by simp)
    have a1 := hs (.x1, .frame 96) (by simp)
    have a2 := hs (.x2, .frame 128) (by simp)
    have a3 := hs (.x3, .frame 32) (by simp)
    have a4 := hs (.x4, .caller 5 0) (by simp)
    change t.gpr .x4 = L.scr + 0#64 at a4
    rw [BitVec.add_zero] at a4
    exact mul_ready hL ⟨a0, a1, a2, a3, a4⟩
  · intro a b ar aw br bw h
    have hsp := two_sp h
    exact ⟨hsp, call_gpr_eq (p := (.x0, .caller 0 32)) h (by simp) (by decide),
      call_gpr_eq (p := (.x1, .frame 96)) h (by simp) (by decide),
      call_gpr_eq (p := (.x2, .frame 128)) h (by simp) (by decide),
      call_gpr_eq (p := (.x3, .frame 32)) h (by simp) (by decide),
      call_gpr_eq (p := (.x4, .caller 5 0)) h (by simp) (by decide)⟩

theorem saveSecret_ct :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block saveSecret)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_sp h) (by taint_decide)) ?_ ?_
  · intro t hc _
    exact WP.mono (saveSecret_ok hc rfl) fun _ h => ⟨h.1, trivial⟩
  · intro t hc _
    exact WP.mono (saveSecret_ok hc rfl) fun _ h => ⟨h.1, trivial⟩

theorem wipe_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block wipe)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_sp h) (by taint_decide)) ?_ ?_
  · intro t hc _
    exact WP.mono (wipe_ok hc hL) fun _ h => ⟨h.1, trivial⟩
  · intro t hc _
    exact WP.mono (wipe_ok hc hL) fun _ h => ⟨h.1, trivial⟩

end VG.Proof.Ed25519.AArch64.SignCached
end

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole VG.Impl.Ed25519.AArch64.SignCached
variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem reduce_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (d : Nat) (hd : d + 32 ≤ 256)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (reduceArgs d)) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (reduce d)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hv : Whole.valid (.frame d) := by change d < 4096; omega
  have hvall : ∀ p : Reg × Value, p ∈ [(.x0, .frame d), (.x1, .frame 192), (.x2, .caller 5 0)] → Whole.valid p.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl)
    · exact hv
    · decide
    · decide
  exact (setup_ct hL ha hb _ (by simp) hvall (by simp [preserved]) ht).seq
    (reduce_call_ct hL ha hb d hd)

theorem base_ct [VG.Proof.Ed25519.AArch64.Divstep.Sound] (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True)
      (callWith baseArgs "vg_ed25519_scalar_base" Impl.Ed25519.AArch64.scalarBase)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb [(.x0, .caller 0 0), (.x1, .frame 96), (.x2, .caller 5 0)]
    (by decide) (by decide) (by decide) (by taint_decide)).seq
    (base_call_ct hL ha hb)

theorem mul_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True)
      (callWith mulAddArgs "vg_ed25519_scalar_mul_add" Impl.Ed25519.AArch64.scalarMulAdd)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb [(.x0, .caller 0 32), (.x1, .frame 96), (.x2, .frame 128),
    (.x3, .frame 32), (.x4, .caller 5 0)]
    (by decide) (by decide) (by decide) (by taint_decide)).seq
    (mul_call_ct hL ha hb)

/-- Signing after a first step related to itself, as the copy of a cached digest is. -/
theorem bodyFrom_ct [VG.Proof.Ed25519.AArch64.Divstep.Sound] (backend : Backend) {first : Prog isa}
    (hfirst : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) first
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True))
    (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (bodyFrom first backend.code backend.suffix)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) :=
  (hfirst.seq saveSecret_ct).seq
    (((hashNonce_ct backend hL ha hb).seq ((reduce_ct hL ha hb 96 (by decide) (by taint_decide)).seq
      (base_ct hL ha hb))).seq
      (((hashChallenge_ct backend hL ha hb).seq ((reduce_ct hL ha hb 128 (by decide) (by taint_decide)).seq
        (mul_ct hL ha hb))).seq (wipe_ct hL)))

end VG.Proof.Ed25519.AArch64.SignCached
end

/-! Merged from `Proof.Ed25519.AArch64.SignCached.CT`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached

theorem lay_eq {n : Nat} {key : State → Prop} {post : State → State → Prop} {s t : State}
    (hp : (signLocalWith n key post).pub s t) : lay n s = lay n t := by
  obtain ⟨sp, h0, h1, h2, h3, h4, h5, hsy⟩ := hp
  simp only [lay, Whole.base, sp, h0, h1, h2, h3, h4, h5, hsy]

end VG.Proof.Ed25519.AArch64.SignCached
end

/-! Merged from `Proof.Ed25519.AArch64.SignCached.Contract`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.SignCached.Sat`. -/
section
/-! A satisfiability witness with a matching seed and cached public key. -/
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64

def satSeed : List Byte := Spec.Ed25519.bytesAt (fun _ => 0) 0x2000 32
def satKey : List Byte := Spec.Ed25519.publicKey satSeed

theorem satKey_length : satKey.length = 32 := by
  simp only [satKey, Spec.Ed25519.publicKey, Spec.Ed25519.encodePoint, Spec.Ed25519.encodeLE,
    List.length_map, List.length_range]

end VG.Proof.Ed25519.AArch64.SignCached
end
end

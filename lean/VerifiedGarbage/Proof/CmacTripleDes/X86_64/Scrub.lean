module

public import VerifiedGarbage.Spec.Cmac.TripleDesContract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86_64.Frame
import VerifiedGarbage.Proof.CmacTripleDes.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Lit
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.RoundLit
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.KeysLit
meta import VerifiedGarbage.Spec.Cmac.TripleDesContract
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86_64.Frame
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Lit
meta import VerifiedGarbage.Proof.CmacTripleDes.X86_64.RoundLit
meta import VerifiedGarbage.Proof.CmacTripleDes.X86_64.KeysLit

/-!
# Streaming TDEA-CMAC on x86-64, without secret residue

`vg_cmac_triple_des_stream_init`, `_absorb` and `_finish`, each followed by
`Impl.Scrub.X86_64.scrubTail` (`X86_64.Scrub.withScrub`), which clears the
registers and the granules of its stack that the residue analysis
(`X86_64.RTaint`) finds may hold secrets. Their postconditions read the
memory on return only within the buffers (`X86_64.Scrub.PostOut`): the state
(`repr_congr`) and the MAC.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub

/-! ## Locality -/

section

variable {m₁ m₂ : Mem}

/-- The memory agrees on the `n` bytes at `p`, from its agreeing on a
region of at least `n` bytes there. -/
theorem agree_of {p : Addr} {L n : Nat} (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) (hn : n ≤ L) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact VG.Offset.contains_base _ (by omega) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega

/-- The streaming state depends only on its 416 bytes. -/
theorem repr_congr {p : Addr} {key msg : List Byte}
    (h : ∀ i < 416, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i))
    (hr : Spec.Cmac.tdesRepr m₁ p key msg) : Spec.Cmac.tdesRepr m₂ p key msg := by
  rw [Stream.repr_iff] at hr ⊢
  obtain ⟨hk, hc, hh⟩ := hr
  have hle := Stream.held_le msg.length
  refine ⟨hk.congr fun i hi => h i (by omega), ?_, ?_⟩
  · rw [show p + 400 = p + BitVec.ofNat 64 400 from rfl, Stream.bytesAt_congr (m := m₁) fun i hi => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact h _ (by omega)]
    exact hc
  · rw [show p + 408 = p + BitVec.ofNat 64 408 from rfl, Stream.bytesAt_congr (m := m₁) fun i hi => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact h _ (by omega)]
    exact hh

end

/-! ## Postconditions -/

theorem initOut : PostOut (Spec.Cmac.tdesStreamInitContract X86_64.abi 648) (Spec.Cmac.tdesStreamInitSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨k, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨kl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.Cmac.tdesStreamInitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    show Spec.Cmac.tdesRepr m₂ st _ _
    exact repr_congr (agree_of hb.1 (by decide)) h

theorem absorbOut : PostOut (Spec.Cmac.tdesAbsorbContract X86_64.abi 696) (Spec.Cmac.tdesAbsorbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨c, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨d, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.Cmac.tdesAbsorbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    show ∀ key msg, Spec.Cmac.tdesRepr m st key msg → _ → _ → Spec.Cmac.tdesRepr m₂ st key _
    intro key msg hr hc hl
    exact repr_congr (agree_of hb.1 (by decide)) (h key msg hr hc hl)

theorem finishOut : PostOut (Spec.Cmac.tdesFinishContract X86_64.abi 648) (Spec.Cmac.tdesFinishSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨c, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨o, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.Cmac.tdesFinishSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    show ∀ key msg, Spec.Cmac.tdesRepr m st key msg → _ → _ → Spec.Aes.bytesAt m₂ o 8 = _
    intro key msg hr hc hl
    rw [Stream.bytesAt_congr (agree_of hb.2 (by decide))]
    exact h key msg hr hc hl

/-! ## The registrations -/

/-- `vg_cmac_triple_des_stream_init`'s code. -/
abbrev initCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratch 648 .rcx Impl.CmacTripleDes.Stream.X86_64.streamInit

def initKs : List Nat := keep_for% Spec.Cmac.tdesStreamInitApi.sig 648 initCode []

theorem initOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Cmac.tdesStreamInitApi.sig 648 []) initCode
      h).any (RScrub.resOkB · 648 initKs (Impl.Scrub.X86_64.chunks 648)) = true :=
  RScrub.Analysed.ok_of initKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_cmac_triple_des_stream_init`. -/
def initReg : Registration Spec.Cmac.tdesStreamInitApi X86_64.target :=
  withScrub {
    code := initCode
    stack := 648
    verified := Proof.CmacTripleDes.Stream.X86_64.init_framed } initOut [] (pubOk_nil _) (some ⟨initKs, initOk⟩)

/-- `vg_cmac_triple_des_absorb`'s code. -/
abbrev absorbCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratch 696 .r8 Impl.CmacTripleDes.Stream.X86_64.absorb

def absorbKs : List Nat := keep_for% Spec.Cmac.tdesAbsorbApi.sig 696 absorbCode []

theorem absorbOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Cmac.tdesAbsorbApi.sig 696 []) absorbCode
      h).any (RScrub.resOkB · 696 absorbKs (Impl.Scrub.X86_64.chunks 696)) = true :=
  RScrub.Analysed.ok_of absorbKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_cmac_triple_des_absorb`. -/
def absorbReg : Registration Spec.Cmac.tdesAbsorbApi X86_64.target :=
  withScrub {
    code := absorbCode
    stack := 696
    verified := Proof.CmacTripleDes.Stream.X86_64.absorb_framed } absorbOut [] (pubOk_nil _) (some ⟨absorbKs, absorbOk⟩)

/-- `vg_cmac_triple_des_finish`'s code. -/
abbrev finishCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratch 648 .rcx Impl.CmacTripleDes.Stream.X86_64.finish

def finishKs : List Nat := keep_for% Spec.Cmac.tdesFinishApi.sig 648 finishCode []

theorem finishOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Cmac.tdesFinishApi.sig 648 []) finishCode
      h).any (RScrub.resOkB · 648 finishKs (Impl.Scrub.X86_64.chunks 648)) = true :=
  RScrub.Analysed.ok_of finishKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_cmac_triple_des_finish`. -/
def finishReg : Registration Spec.Cmac.tdesFinishApi X86_64.target :=
  withScrub {
    code := finishCode
    stack := 648
    verified := Proof.CmacTripleDes.Stream.X86_64.finish_framed } finishOut [] (pubOk_nil _) (some ⟨finishKs, finishOk⟩)

end VG.Proof.CmacTripleDes.X86_64.Scrub

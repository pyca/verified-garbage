module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrRoundAll
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages
import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedFrame
import VerifiedGarbage.Proof.Bignum.X86_64.Template

/-! ### `RsaKeyGen.X86_64.SharedWitness`, which only this module used -/

section

/-!
# A candidate on x86-64: one round of Miller–Rabin

Prepare the witness in Montgomery form for the callable shared round.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

def witnessRanges (w : Nat) : List (Nat × Nat) :=
  witRanges w ++ [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))]

/-- Load RSA's next witness and convert it to Montgomery form. -/
theorem sharedWitness_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm : Nat}
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c bm)
    (hR2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c) (hodd : c % 2 = 1) (hc1 : 1 < c)
    (hb : Spec.RsaKeyGen.bitLength (c - 1) = 64 * w)
    {rp : Addr} {used : Nat} {r : List Byte} (hR : word s.mem B (8 * kRand) = rp)
    (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hsrc : Src s B Z rp r) (hlen : used + 8 * w ≤ r.length) :
    WP isa (seqs (mrWitness ++ [M.mm aXm aX aR2])) s fun t =>
      MrCtx t B Z w mi c bm ∧
      wv t.mem B (slot w aXm) w = (wtOf c w used r).1 % c * 2 ^ (64 * w) % c ∧
      wv t.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kU) =
        mask (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).2 ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 (used + 8 * w) ∧
      Frm B (witnessRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hg := hc.good
  have hZ := hd.z
  have hXZ := hd.x
  have hw4 := hd.w4
  have hw' : w < 2 ^ 31 := by have := hd.w128; omega_using [this]
  have hn := hg.scr.nowrap
  have hRc : Nat.Coprime (2 ^ (64 * w)) c := VG.Proof.Bignum.coprime_pow2 hodd _
  have hc0 : 0 < c := by omega_using [hc1]
  refine wp_seqs_append (by simp [mrWitness]) (by simp) ?_
  refine WP.mono (mrWitness_ok hd hc hodd hb hR hU hK (VG.Proof.RsaKeyGen.X86_64.Src.seg hsrc hlen) (by
    simp only [VG.Proof.RsaKeyGen.seg, List.length_take, List.length_drop]; omega_using [hlen]))
    fun s₁ ⟨hc₁, hx₁, hu₁, hus₁, hf₁, k₁⟩ => ?_
  dsimp only [wtOf]
  generalize hwt : Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w))) = wt
    at hx₁ hu₁ ⊢
  have hR2₁ : wv s₁.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c := by
    rw [hf₁.wv_eq (d := slot w aR2) (k := w) (by simp only [witRanges]; rng_disj)
      (by have := slot_le (w := w) (show aR2 < 8 by decide); omega_using [hZ, hn, this])]; exact hR2
  -- `b R mod c` into `aXm`.
  simp only [seqs]
  refine WP.mono (M.mm_ok hc₁.good hZ (by omega_using [hw4]) hw' (o := aXm) (a := aX) (b := aR2) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hc₁.inv
    (by rw [hR2₁, hc₁.n]; exact Nat.mod_lt _ hc0)) fun s₂ ⟨hg₂, hlt₂, hy₂, ha₂, k₂⟩ => ?_
  rw [hc₁.n] at hlt₂ hy₂
  rw [hx₁, hR2₁] at hy₂
  have hXm : wv s₂.mem B (slot w aXm) w = Spec.Rsa.powMod wt.1 1 c * 2 ^ (64 * w) % c := by
    rw [← Nat.mod_eq_of_lt hlt₂, VG.Proof.Bignum.powMod_eq, Nat.pow_one, Nat.mod_mul_mod]
    refine VG.Proof.Bignum.mont_cancel hRc ?_
    rw [hy₂, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  have hf₂ : Frm B [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))] s₁.mem s₂.mem :=
    Frm.of_arrays ha₂ (by simp)
  have hc₂ : MrCtx s₂ B Z w mi c bm := hc₁.of_frm hd hf₂ hg₂.scr hg₂.rdi (by rng_disj) (by rng_disj) (by rng_disj)
    (by rng_disj) (by rng_disj)
  have hf : Frm B (witnessRanges w) s.mem s₂.mem :=
    (hf₁.mono (fun r hr => List.mem_append_left _ hr)).trans
      (hf₂.mono (fun r hr => List.mem_append_right _ hr))
  refine ⟨hc₂, ?_, ?_, ?_, ?_, hf, (k₁.trans k₂).mono (by decide)⟩
  · simpa only [VG.Proof.Bignum.powMod_eq, Nat.pow_one] using hXm
  · rw [hf₂.wv_eq (d := slot w aR2) (k := w) (by rng_disj)
      (by have := slot_le (w := w) (show aR2 < 8 by decide); omega_arith)]
    exact hR2₁
  · rw [hf₂.word_eq (d := 8 * kU) (by rng_disj) (by unfold kU sFn; omega_arith)]
    exact hu₁
  · rw [hf₂.word_eq (d := 8 * kUsed) (by rng_disj) (by unfold kUsed sFn; omega_arith)]
    exact hus₁

end VG.Proof.RsaKeyGen.X86_64

end

end


/-!
# The candidate's Montgomery multiplications as calls

The candidate multiplies by `mm`, calls that inline to the backend's
`M.mm` (`MmCalls`). A piece of it that calls only `mm` runs as its inline
form does but for the return address, which a call stores in the 8 bytes
below `rsp` (`hole`, within the 128 the round's call uses: `SharedEnv`).
These bytes are off the working space, so what the inline run proves of
the working space holds after the calls, with `SharedFrame` for `Frm`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MillerRabin.X86_64
open VG.Proof.MlKem.X86_64

/-- `mm` calls functions that inline to `M.mm`. -/
structure MmCalls (M : Mont) (mm : Nat → Nat → Nat → Prog isa) : Prop where
  ok : ∀ o a b, (mm o a b).InlineOk = true
  inline : ∀ o a b, (mm o a b).inline = M.mm o a b

theorem hole_below (sp : Addr) : Region.Sub (hole sp) (below sp 128) :=
  below_sub (sp := sp) (a := 8) (b := 128) (by decide) (by decide)

theorem SharedEnv.hole_clear {B sp : Addr} {Z : Nat} {s : State} (he : SharedEnv B Z sp s) :
    Clear (hole (s.gpr .rsp)) s := by
  rw [he.rsp]
  exact fun r hr => (he.clear r hr).sub_right (hole_below sp)

theorem SharedEnv.hole_miss {B sp : Addr} {Z : Nat} {s : State} (he : SharedEnv B Z sp s) {x : Addr}
    (hx : ofs B x < Z) : ¬ (hole sp).Contains x 1 := by
  intro hc
  have hd := he.room.disjoint
  rw [he.rsp] at hd
  exact hd x hx (hole_below sp x hc)

/-- The patched state agrees with the inline one on the working space. -/
theorem SharedEnv.patch_frm {B sp : Addr} {Z : Nat} {s b : State} {hv : Mem} {u : Nat → BitVec 64}
    (he : SharedEnv B Z sp s) : Frm B [(Z, 2 ^ 64)] b.mem (b.patch (hole sp) hv u).mem := by
  intro x hx
  have hx := hx _ (List.mem_singleton_self _)
  have hlt : ofs B x < 2 ^ 64 := BitVec.isLt _
  exact State.patch_mem (he.hole_miss (by omega_using [hx, hlt]))

/-- What the inline run changes, the run with calls changes, but for the
return address. -/
theorem Frm.patch_shared {B sp : Addr} {rs : List (Nat × Nat)} {m : Mem} {b : State} {hv : Mem}
    {u : Nat → BitVec 64} (hf : Frm B rs m b.mem) :
    SharedFrame B sp rs m (b.patch (hole sp) hv u).mem := by
  intro x hx hr
  rw [State.patch_mem fun hc => hx _ (List.mem_singleton_self _) (hole_below sp x hc)]
  exact hf x hr

theorem SharedEnv.patch_good {B sp : Addr} {Z w : Nat} {mi : BitVec 64} {s b : State} {hv : Mem}
    {u : Nat → BitVec 64} (he : SharedEnv B Z sp s) (hg : Good b B Z w mi) (hZ : 128 ≤ Z) :
    Good (b.patch (hole sp) hv u) B Z w mi :=
  ⟨hg.scr.congr rfl, hg.rdi, Hdr.of_frm hg.hdr he.patch_frm fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hZ⟩

theorem SharedEnv.patch_wv {B sp : Addr} {Z d k : Nat} {s b : State} {hv : Mem}
    {u : Nat → BitVec 64} (he : SharedEnv B Z sp s) (hd : d + 8 * k ≤ Z) (hn : B.toNat + Z ≤ 2 ^ 64) :
    wv (b.patch (hole sp) hv u).mem B d k = wv b.mem B d k :=
  he.patch_frm.wv_eq (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact Or.inl hd)
    (by omega_using [hd, hn])

theorem SharedEnv.patch_word {B sp : Addr} {Z d : Nat} {s b : State} {hv : Mem}
    {u : Nat → BitVec 64} (he : SharedEnv B Z sp s) (hd : d + 8 ≤ Z) (hn : B.toNat + Z ≤ 2 ^ 64) :
    word (b.patch (hole sp) hv u).mem B d = word b.mem B d :=
  he.patch_frm.word_eq (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact Or.inl hd)
    (by omega_using [hd, hn])

theorem SharedEnv.patch_mrCtx {B sp : Addr} {Z w : Nat} {mi : BitVec 64} {c bm : Nat} {s b : State}
    {hv : Mem} {u : Nat → BitVec 64} (he : SharedEnv B Z sp s) (hc : MrCtx b B Z w mi c bm)
    (hd : MrDims B Z w) : MrCtx (b.patch (hole sp) hv u) B Z w mi c bm := by
  have hx := hd.x
  have h128 : 128 ≤ Z := by
    have := slot_le (w := w) (show aN < 8 by decide)
    unfold slot aN hdrBytes at *; omega_arith
  have hsep : ∀ j, j ≤ aRm1 → ∀ r ∈ [(Z, 2 ^ 64)], slot w j + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
    intro j hj r hr
    simp only [List.mem_singleton] at hr
    subst hr
    have : slot w j ≤ slot w aRm1 := by
      unfold slot; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hj) _
    exact Or.inl (by omega_using [hx, this])
  exact MrCtx.of_frm hc hd he.patch_frm (hc.good.scr.congr rfl) hc.good.rdi
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h128)
    (hsep aN (by decide)) (hsep aB (by decide)) (hsep aR1 (by decide)) (hsep aRm1 (by decide))

/-! ## The pieces that multiply -/

theorem montSetup_inlineOk {mm : Nat → Nat → Nat → Prog isa} (hm : ∀ o a b, (mm o a b).InlineOk = true) :
    (seqs (montSetup mm)).InlineOk = true := by
  rw [inlineOk_seqs]
  unfold montSetup
  simp only [List.all_cons, List.all_nil, hm, Bool.true_and, Bool.and_true]
  decide +kernel

theorem montSetup_inline (mm : Nat → Nat → Nat → Prog isa) :
    (seqs (montSetup mm)).inline = seqs (montSetup fun o a b => (mm o a b).inline) := by
  unfold montSetup
  simp only [inline_seqs, List.map_cons, List.map_nil]
  simp (disch := decide) only [inline_of_noCalls]

theorem witness_inlineOk {mm : Nat → Nat → Nat → Prog isa} (hm : ∀ o a b, (mm o a b).InlineOk = true) :
    (seqs (mrWitness ++ [mm aXm aX aR2])).InlineOk = true := by
  rw [inlineOk_seqs, List.all_append, List.all_cons, List.all_nil, hm, Bool.true_and, Bool.and_true]
  decide +kernel

theorem witness_inline (mm : Nat → Nat → Nat → Prog isa) :
    (seqs (mrWitness ++ [mm aXm aX aR2])).inline = seqs (mrWitness ++ [(mm aXm aX aR2).inline]) := by
  simp only [inline_seqs, List.map_append, List.map_cons, List.map_nil]
  simp (disch := decide) only [map_inline_of_noCalls]

theorem MmCalls.montSetup {M : Mont} {mm : Nat → Nat → Nat → Prog isa} (hm : MmCalls M mm) :
    (seqs (montSetup mm)).inline = seqs (montSetup M.mm) := by
  rw [montSetup_inline]
  congr 2
  funext o a b
  exact hm.inline o a b

theorem MmCalls.witness {M : Mont} {mm : Nat → Nat → Nat → Prog isa} (hm : MmCalls M mm) :
    (seqs (mrWitness ++ [mm aXm aX aR2])).inline = seqs (mrWitness ++ [M.mm aXm aX aR2]) := by
  rw [witness_inline, hm.inline]

/-- `montSetup_ok`, with calls. -/
theorem montSetup_call_ok (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hm : MmCalls M mm)
    {s : State} {B sp : Addr} {Z w : Nat} {mi : BitVec 64} {N : Nat} (henv : SharedEnv B Z sp s)
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hXZ : slot w aRm1 + 8 * (w + 2) ≤ Z) (hw : 4 ≤ w) (hw64 : w ≤ 64)
    (hn : wv s.mem B (slot w aN) w = N) (hodd : N % 2 = 1) (htop : 2 ^ (64 * w - 1) ≤ N) :
    WP isa (seqs (montSetup mm)) s fun t => ∃ mi' : BitVec 64, Good t B Z w mi' ∧
      ((word t.mem B (slot w aN)).toNat * mi'.toNat + 1) % 2 ^ 64 = 0 ∧
      wv t.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧
      wv t.mem B (slot w aR1) w = 2 ^ (64 * w) % N ∧
      wv t.mem B (slot w aRm1) w = N - 2 ^ (64 * w) % N ∧
      word t.mem B (8 * kChecks) = BitVec.ofNat 64 (Proof.RsaKeyGen.checksW w) ∧
      SharedFrame B sp (msRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hnw := hg.scr.nowrap
  have h128 : 128 ≤ Z := by have := hdr_lt_slot w 8 (show 31 < 32 by decide); omega_arith
  have hrun := montSetup_ok M hg hZ hXZ hw hw64 hn hodd htop
  rw [← hm.montSetup] at hrun
  refine WP.mono (WP.of_inline (montSetup_inlineOk hm.ok) henv.hole_clear hrun) ?_
  rintro _ ⟨b, hv, u, rfl, -, mi', hg', hinv, hr2, hr1, hrm, hch, hf, hk⟩
  rw [henv.rsp]
  have hs := fun {d} (h : d + 8 ≤ Z) => henv.patch_word (b := b) (hv := hv) (u := u) h hnw
  have hv' := fun {d} (h : d + 8 * w ≤ Z) => henv.patch_wv (b := b) (hv := hv) (u := u) (k := w) h hnw
  have hsl := fun j (hj : j < 8) => slot_le (w := w) hj
  refine ⟨mi', henv.patch_good hg' h128, ?_, ?_, ?_, ?_, ?_, Frm.patch_shared hf, hk⟩
  · rw [hs (by have := hsl aN (by decide); omega_arith)]; exact hinv
  · rw [hv' (by have := hsl aR2 (by decide); omega_arith)]; exact hr2
  · rw [hv' (by unfold slot aR1 aRm1 at *; omega_arith)]; exact hr1
  · rw [hv' (by omega_arith)]; exact hrm
  · rw [hs (by have := hdr_lt_slot w 8 (show kChecks < 32 by decide); omega_arith)]; exact hch

/-- `sharedWitness_ok`, with calls. -/
theorem sharedWitness_call_ok (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hm : MmCalls M mm)
    {s : State} {B sp : Addr} {Z w : Nat} {mi : BitVec 64} {c bm : Nat} (henv : SharedEnv B Z sp s)
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c bm)
    (hR2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c) (hodd : c % 2 = 1) (hc1 : 1 < c)
    (hb : Spec.RsaKeyGen.bitLength (c - 1) = 64 * w)
    {rp : Addr} {used : Nat} {r : List Byte} (hR : word s.mem B (8 * kRand) = rp)
    (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hsrc : Src s B Z rp r) (hlen : used + 8 * w ≤ r.length) :
    WP isa (seqs (mrWitness ++ [mm aXm aX aR2])) s fun t =>
      MrCtx t B Z w mi c bm ∧
      wv t.mem B (slot w aXm) w = (wtOf c w used r).1 % c * 2 ^ (64 * w) % c ∧
      wv t.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kU) =
        mask (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).2 ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 (used + 8 * w) ∧
      SharedFrame B sp (witnessRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hnw := hc.good.scr.nowrap
  have hZ := hd.z
  have hx := hd.x
  have hrun := sharedWitness_ok M hd hc hR2 hodd hc1 hb hR hU hK hsrc hlen
  rw [← hm.witness] at hrun
  refine WP.mono (WP.of_inline (witness_inlineOk hm.ok) henv.hole_clear hrun) ?_
  rintro _ ⟨b, hv, u, rfl, -, hcb, hxb, hr2, hu, hus, hf, hk⟩
  rw [henv.rsp]
  have hs := fun {d} (h : d + 8 ≤ Z) => henv.patch_word (b := b) (hv := hv) (u := u) h hnw
  have hv' := fun {d} (h : d + 8 * w ≤ Z) => henv.patch_wv (b := b) (hv := hv) (u := u) (k := w) h hnw
  have hsl := fun j (hj : j < 8) => slot_le (w := w) hj
  refine ⟨henv.patch_mrCtx hcb hd, ?_, ?_, ?_, ?_, Frm.patch_shared hf, hk⟩
  · rw [hv' (by have := hsl aXm (by decide); omega_arith)]; exact hxb
  · rw [hv' (by have := hsl aR2 (by decide); omega_arith)]; exact hr2
  · rw [hs (by have := hdr_lt_slot w 8 (show kU < 32 by decide); omega_arith)]; exact hu
  · rw [hs (by have := hdr_lt_slot w 8 (show kUsed < 32 by decide); omega_arith)]; exact hus

end VG.Proof.RsaKeyGen.X86_64

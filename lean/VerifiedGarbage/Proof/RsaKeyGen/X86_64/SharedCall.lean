module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedWitness
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Bignum.X86_64.Template
import VerifiedGarbage.Proof.Framework.Omega

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
  exact State.patch_mem (he.hole_miss (by omega))

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
    (by omega)

theorem SharedEnv.patch_word {B sp : Addr} {Z d : Nat} {s b : State} {hv : Mem}
    {u : Nat → BitVec 64} (he : SharedEnv B Z sp s) (hd : d + 8 ≤ Z) (hn : B.toNat + Z ≤ 2 ^ 64) :
    word (b.patch (hole sp) hv u).mem B d = word b.mem B d :=
  he.patch_frm.word_eq (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact Or.inl hd)
    (by omega)

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
    exact Or.inl (by omega)
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

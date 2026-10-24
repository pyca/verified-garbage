module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.KSSetup
public import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBytes
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.Inline
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on PPC64LE: numbers into the key working space

`loadAt_vp`: array `j`, zero, := the `n` big-endian bytes at `r6`
(`r8 = n`), readable and apart from the key working space (`load_ok`);
`loadS_vp`: from a claim on `scratch`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE VG.Proof.Mont
open VG.Proof.Rsa.KeyWorkspace (S arr num slot Arrs)
open VG.Proof.Rsa.PPC64LE.Keys (Ws load_ok)
open VG.Impl.Dsa.PPC64LE.Generation

section
variable {G : GP} {STK : Nat} {σ : State} {c : Cfg} {s : State}

/-- Code in the key working space, also reading the regions `rs`. -/
theorem SS.ksWPr (h : SS G STK σ c s) {rs : List Region} (hrs : Covers rs (s.rd ++ s.wr)) {code : Prog isa}
    (hn : code.noCalls = true) {P : State → Prop} (hwp : WP isa code (s.withRegions (s.rd ++ rs) [G.rK]) P)
    {Q : State → Prop}
    (k : ∀ t, P (t.withRegions (s.rd ++ rs) [G.rK]) → t.rd = s.rd → t.wr = s.wr → Frame [G.rK] s.mem t.mem →
      Q t) :
    WP isa code s Q :=
  regionModel.wp_narrow (r := s.rd ++ rs) (w := [G.rK]) hwp
    (Covers.append_left (Covers.append_left (Covers.left (Covers.refl _)) hrs) h.kcov.2.right) h.kcov.2
    (Code.noFrames_of_noCalls hn) (.inl hn) fun _ s' _ hr hw' f p => k s' p hr hw' f

end

theorem past_of_disjoint' {B : Addr} {Z : Nat} {r : Region} (hd : r.Disjoint ⟨B, Z⟩) {a : Addr}
    (ha : r.Contains a 1) : Z ≤ (a - B).toNat := by
  have := hd a ha
  simp only [Region.Contains] at this
  omega

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The taint analysis of a load, its source and length public. -/
abbrev CertL (j : Nat) : Prop := ∃ hc, (VG.Taint.check VG.PPC64LE.taint
  (Taint.ofRegs [.r28, .r29, .r30, .r31, .r6, .r8]) (VG.Impl.Rsa.PPC64LE.CrtValues.load j) hc).isSome = true

/-- Array `j`, zero, := the `n` bytes `bs` at `r6` (`r8 = n`), readable and
apart from the key working space. -/
theorem loadAt_vp {j n : Nat} {P : Addr} {bs : List Byte} (cert : CertL j)
    (hj : j < nArrs) (hjl : j ∈ c.live) (hj0 : c.A j = 0) (hn0 : 0 < n) (hnw : n ≤ 4 * G.w)
    (hsrc : ∀ σ s, St G c X σ s → Covers [⟨P, n⟩] (s.rd ++ s.wr) ∧
      Region.Disjoint ⟨P, n⟩ G.rK ∧ Spec.Rsa.bytesAt s.mem P n = bs) :
    VP (fun σ s => (KSt G c X σ s ∧ TopAll G s.mem) ∧ s.gpr .r6 = P ∧ s.gpr .r8 = BitVec.ofNat 64 n)
      (VG.Impl.Rsa.PPC64LE.CrtValues.load j)
      (fun σ t => KSt G { c with A := KU c.A j (Spec.Dsa.decodeBE bs), live := j :: c.live } X σ t ∧
        TopAll G t.mem) := by
  refine VP.pub (G := G) (fun σ s hs => ⟨hs.1.1.1.1.gi.r28, by rw [hs.1.1.1.1.gi.sp, ← hs.1.1.1.1.gi.hG]; rfl⟩)
    [.r29, .r30, .r31, .r6, .r8] cert
    (fun σ₁ σ₂ s₁ s₂ ⟨⟨⟨_, a⟩, _⟩, a6, a8⟩ ⟨⟨⟨_, b⟩, _⟩, b6, b8⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [a.r29, b.r29]
      · rw [a.r30, b.r30]
      · rw [a.r31, b.r31]
      · rw [a6, b6]
      · rw [a8, b8]) fun σ s ⟨⟨⟨⟨h, x⟩, kr⟩, top⟩, p6, p8⟩ => ?_
  obtain ⟨hR, sep, b⟩ := hsrc σ s ⟨h, x⟩
  have l := h.lens
  have hw := h.wsWith kr (s.rd ++ [⟨P, n⟩])
  have nw := hw.nowrap
  have fa := hw.arr_fit hj
  have z : val32 s.mem G.KB (arr G.w j) G.w = 0 := by
    have := h.arrs.get hjl; rw [hj0] at this; exact this
  have w96 : G.w ≤ 96 := by simp only [GP.w]; rcases l with e | e | e <;> rw [e] <;> decide
  have hc : ∀ i < n, (⟨P, n⟩ : Region).Contains (P + BitVec.ofNat 64 i) 1 := fun i hi =>
    Offset.contains_base _ (by omega) (by omega)
  refine h.ksWPr hR rfl (P := fun t => Ws t G.KB (kz G.pLen) G.w nArrs ∧ KKeep G.KB G.w [j] [] s.mem t.mem ∧
      num t.mem G.KB G.w j = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P n) ∧
      VG.Proof.Bignum.PPC64LE.Keep [.r0, .r5, .r6, .r8] (s.withRegions (s.rd ++ [⟨P, n⟩]) [G.rK]) t ∧
      VG.Proof.Bignum.Outside G.KB (arr G.w j) (4 * G.w) s.mem t.mem) ?_ ?_
  · refine WP.mono (load_ok hw hj (by decide) p6 p8 hn0 hnw
      (fun i hi => ⟨⟨P, n⟩, List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _)), hc i hi⟩)
      (fun i hi x hx e => by subst e; exact absurd (past_of_disjoint' sep (hc i hi)) (Nat.not_le.mpr hx))
      fun p hp => by rw [← VG.Proof.Bignum.PPC64LE.off_add]; exact VG.Proof.Bignum.byte_zero_of_val32 z hp)
      fun t ⟨w, k, v, r, o⟩ => ⟨w, k, v, r, o⟩
  · intro t ⟨_, k, v, R, o⟩ hr hw' fK
    simp only [State.withRegions_mem] at v
    have vw : num t.mem G.KB G.w j = Spec.Dsa.decodeBE bs := by rw [v, b, VG.Proof.Dsa.decodeBE_os2ip]
    have R' : Keep [.r0, .r5, .r6, .r8] s t := ⟨R.gpr, hr, hw'⟩
    refine ⟨⟨⟨h.of_op R' R.sp fK hj k vw, x⟩, kr.of_keep R'⟩, fun i hi hne => ?_⟩
    simp only [State.withRegions_mem] at k o
    have fi := hw.arr_fit hi
    by_cases e : i = j
    · subst e
      rw [VG.Proof.Mont.Outside.w32 o (.inr (Nat.le_refl _)) (by have := hw.fit64 hi; simp only [S] at this; omega)]
      exact top i hi hne
    · rw [k.word (j := i) (i := G.w) (by simp only [S]; omega) (by simpa using Ne.symm e) (by simp)
        (hw.fit64 hi)]
      exact top i hi hne

/-- `loadAt_vp` without the top words: array `j`, zero, := the `n` bytes `bs`
at `r6` (`r8 = n`). -/
theorem loadZ_vp {j n : Nat} {P : Addr} {bs : List Byte} (cert : CertL j)
    (hj : j < nArrs) (hjl : j ∈ c.live) (hj0 : c.A j = 0) (hn0 : 0 < n) (hnw : n ≤ 4 * G.w)
    (hsrc : ∀ σ s, St G c X σ s → Covers [⟨P, n⟩] (s.rd ++ s.wr) ∧
      Region.Disjoint ⟨P, n⟩ G.rK ∧ Spec.Rsa.bytesAt s.mem P n = bs) :
    VP (fun σ s => KSt G c X σ s ∧ s.gpr .r6 = P ∧ s.gpr .r8 = BitVec.ofNat 64 n)
      (VG.Impl.Rsa.PPC64LE.CrtValues.load j)
      (KSt G { c with A := KU c.A j (Spec.Dsa.decodeBE bs), live := j :: c.live } X) := by
  refine VP.pub (G := G) (fun σ s hs => ⟨hs.1.1.1.gi.r28, by rw [hs.1.1.1.gi.sp, ← hs.1.1.1.gi.hG]; rfl⟩)
    [.r29, .r30, .r31, .r6, .r8] cert
    (fun σ₁ σ₂ s₁ s₂ ⟨⟨_, a⟩, a6, a8⟩ ⟨⟨_, b⟩, b6, b8⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [a.r29, b.r29]
      · rw [a.r30, b.r30]
      · rw [a.r31, b.r31]
      · rw [a6, b6]
      · rw [a8, b8]) fun σ s ⟨⟨⟨h, x⟩, kr⟩, p6, p8⟩ => ?_
  obtain ⟨hR, sep, b⟩ := hsrc σ s ⟨h, x⟩
  have hw := h.wsWith kr (s.rd ++ [⟨P, n⟩])
  have z : val32 s.mem G.KB (arr G.w j) G.w = 0 := by
    have := h.arrs.get hjl; rw [hj0] at this; exact this
  have w96 : G.w ≤ 96 := by simp only [GP.w]; rcases h.lens with e | e | e <;> rw [e] <;> decide
  have hc : ∀ i < n, (⟨P, n⟩ : Region).Contains (P + BitVec.ofNat 64 i) 1 := fun i hi =>
    Offset.contains_base _ (by omega) (by omega)
  refine h.ksWPr hR rfl (P := fun t => Ws t G.KB (kz G.pLen) G.w nArrs ∧ KKeep G.KB G.w [j] [] s.mem t.mem ∧
      num t.mem G.KB G.w j = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P n) ∧
      VG.Proof.Bignum.PPC64LE.Keep [.r0, .r5, .r6, .r8] (s.withRegions (s.rd ++ [⟨P, n⟩]) [G.rK]) t) ?_ ?_
  · refine WP.mono (load_ok hw hj (by decide) p6 p8 hn0 hnw
      (fun i hi => ⟨⟨P, n⟩, List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _)), hc i hi⟩)
      (fun i hi x hx e => by subst e; exact absurd (past_of_disjoint' sep (hc i hi)) (Nat.not_le.mpr hx))
      fun p hp => by rw [← VG.Proof.Bignum.PPC64LE.off_add]; exact VG.Proof.Bignum.byte_zero_of_val32 z hp)
      fun t ⟨w, k, v, r, _⟩ => ⟨w, k, v, r⟩
  · intro t ⟨_, k, v, R⟩ hr hw' fK
    simp only [State.withRegions_mem] at v k
    have vw : num t.mem G.KB G.w j = Spec.Dsa.decodeBE bs := by rw [v, b, VG.Proof.Dsa.decodeBE_os2ip]
    have R' : Keep [.r0, .r5, .r6, .r8] s t := ⟨R.gpr, hr, hw'⟩
    exact ⟨⟨h.of_op R' R.sp fK hj k vw, x⟩, kr.of_keep R'⟩

/-- Array `j`, zero, := the bytes `bs` that a claim puts at byte `o` of `scratch`. -/
theorem loadS_vp {j o n : Nat} {bs : List Byte} (cert : CertL j)
    (hj : j < nArrs) (hjl : j ∈ c.live) (hj0 : c.A j = 0) (hbs : (o, bs) ∈ c.cl) (hn : bs.length = n)
    (hn0 : 0 < n) (hnw : n ≤ 4 * G.w) (ho : o < 2 ^ 15) (hn15 : n < 2 ^ 15) :
    VP (fun σ s => KSt G c X σ s ∧ TopAll G s.mem) (loadS j o n)
      (fun σ t => KSt G { c with A := KU c.A j (Spec.Dsa.decodeBE bs), live := j :: c.live } X σ t ∧
        TopAll G t.mem) := by
  refine VP.seq (G := fun σ s => (KSt G c X σ s ∧ TopAll G s.mem) ∧ s.gpr .r6 = G.sa o ∧
      s.gpr .r8 = BitVec.ofNat 64 n)
    (VP.pub (G := G) (fun σ s hs => ⟨hs.1.1.1.gi.r28, by rw [hs.1.1.1.gi.sp, ← hs.1.1.1.gi.hG]; rfl⟩) []
      ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block [scr .r6 o, .li .r8 n]), rfl⟩
      (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨⟨⟨h, x⟩, kr⟩, top⟩ => ?_)
    (loadAt_vp cert hj hjl hj0 hn0 hnw fun σ s ⟨h, x⟩ => ?_)
  · refine WP.sp_eq ?_
    refine WP.wr (exec_addi (by decide) ho) fun s₁ u₁ sp₁ _ => ?_
    refine WP.wr (exec_li hn15) fun t u sp _ => WP.block_nil fun _ => ⟨⟨⟨⟨(h.of_upd u₁ sp₁ (by decide)).of_upd u sp
      (by decide), x⟩, (kr.of_keep (ws := [.r6]) ⟨fun r hr => u₁.other r (by simpa using hr), u₁.rd, u₁.wr⟩).of_keep
      (ws := [.r8]) ⟨fun r hr => u.other r (by simpa using hr), u.rd, u.wr⟩⟩, by rw [u.mem, u₁.mem]; exact top⟩, ?_, ?_⟩
    · rw [u.other _ (by decide), u₁.gpr, h.gi.r28]
    · rw [u.gpr]
  · have gi := h.gi
    have big := gi.wBig
    have kb := gi.kBig
    have fit := gi.scrFit
    have inS : G.rScr ∈ s.wr := by rw [gi.wr, gi.pre.wr, gi.hG]; simp
    have ok := h.clOk _ hbs
    simp only [ClOk, hn] at ok
    have b := h.sb _ hbs
    simp only [hn] at b
    refine ⟨(Covers.of_sub (rs' := [G.rScr]) fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact ⟨G.rScr, List.mem_singleton_self _, o, rfl, show o + n ≤ G.scrLen * 8 by omega⟩).trans
      (Covers.of_mem fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact List.mem_append_right _ inS),
      (gi.kdisj ok.2.1 ok.2.2).symm, b⟩

end

end VG.Proof.Dsa.PPC64LE.Gen

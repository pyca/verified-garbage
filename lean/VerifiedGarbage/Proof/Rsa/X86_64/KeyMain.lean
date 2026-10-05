import VerifiedGarbage.Proof.Rsa.X86_64.KeyMod
import VerifiedGarbage.Proof.Rsa.KeyParts
import VerifiedGarbage.Proof.Bignum.X86_64.R2

/-!
# `vg_rsa_check_key` on x86-64: the checks

`main`, from the header `entry` leaves, for a valid modulus and exponent:
the workspace (`setupK_ok`), then each check, and'ed into `sMask`; it
returns `keyValid` as 1 or 0 (`main_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask sN sK)

/-- What `main` starts from: the header `entry` leaves, `e`'s value in
`sEv`, and the byte strings outside the working space. -/
structure MainPre (s : State) (B : Addr) (Z k : Nat) (np pd pp pq pdp pdq pqi : Addr)
    (nb db pb qb dpb dqb qib : List Byte) (ev : Nat) : Prop where
  scr : Scr s B Z
  rdi : s.gpr .rdi = B
  zk : 128 * k ≤ Z
  k1 : 64 ≤ k
  k2 : k ≤ 1024
  nl : nb.length = k
  dl1 : 1 ≤ db.length
  dl2 : db.length ≤ k
  pl1 : 1 ≤ pb.length
  pl2 : pb.length < k
  ql1 : 1 ≤ qb.length
  ql2 : qb.length < k
  dpl : dpb.length = pb.length
  qil : qib.length = pb.length
  dql : dqb.length = qb.length
  hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k
  hN : word s.mem B (8 * sN) = np
  hD : word s.mem B (8 * sD) = pd
  hDl : word s.mem B (8 * sDlen) = BitVec.ofNat 64 db.length
  hP : word s.mem B (8 * sP) = pp
  hPl : word s.mem B (8 * sPlen) = BitVec.ofNat 64 pb.length
  hQ : word s.mem B (8 * sQ) = pq
  hQl : word s.mem B (8 * sQlen) = BitVec.ofNat 64 qb.length
  hDP : word s.mem B (8 * sDP) = pdp
  hDQ : word s.mem B (8 * sDQ) = pdq
  hQI : word s.mem B (8 * sQI) = pqi
  hEv : (word s.mem B (8 * sEv)).toNat = ev
  srN : Src s B Z np nb
  srD : Src s B Z pd db
  srP : Src s B Z pp pb
  srQ : Src s B Z pq qb
  srDP : Src s B Z pdp dpb
  srDQ : Src s B Z pdq dqb
  srQI : Src s B Z pqi qib
  mv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true

/-- The header slots `main`'s setup writes: `w`, the arrays' bases and
`sMask`. -/
def setupSlot (i : Nat) : Bool := i == sW || (8 ≤ i && i < 16) || i == sMask

theorem setupSlot_false : ∀ i < 32, setupSlot i = false → i ≠ 6 ∧ (i < 8 ∨ 16 ≤ i) ∧ i ≠ 22 := by
  decide

/-- The setup: `w`, the bases, `n`, the number 1 and `sMask` all ones. -/
theorem setupK_ok {s : State} {B : Addr} {Z k : Nat} {np pd pp pq pdp pdq pqi : Addr}
    {nb db pb qb dpb dqb qib : List Byte} {ev : Nat}
    (hp : MainPre s B Z k np pd pp pq pdp pdq pqi nb db pb qb dpb dqb qib ev) :
    WP isa (seqs [.block VG.Impl.Rsa.X86_64.head, loadBE, .block [.mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)], setWord aOne .rcx,
        .block [.mov32 .rax (.imm 0), .alu .sub .rax (.imm 1), .store (hdr sMask) .rax]]) s fun t =>
      ∃ minv, KCtx t t B Z ((k + 7) / 8) minv (Spec.Rsa.os2ip nb) ∧ word t.mem B (8 * sMask) = mask true ∧
        (∀ i < 32, setupSlot i = false → word t.mem B (8 * i) = word s.mem B (8 * i)) ∧
        InScr B Z s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ Keep mmRegs s t := by
  have hs := hp.scr
  have hn := hs.nowrap
  have := hp.k1
  have := hp.k2
  have hZ : slot ((k + 7) / 8) 8 ≤ Z := by have := hp.zk; unfold slot hdrBytes; omega
  have h8 := hdr_lt_slot ((k + 7) / 8) 0 (show 31 < 32 by decide)
  have h0 := slot_le (w := (k + 7) / 8) (show 0 < 8 by decide)
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have eM : sMask = 22 := rfl
  have eI : sMinv = 7 := rfl
  have hsl : ∀ r ∈ [(8 * sW, 8), (8 * sArr 0, 64)], r.1 + r.2 ≤ Z := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl) <;> simp only [eW, eA] <;> omega
  have hfw : ∀ i, i ≠ 6 → (i < 8 ∨ 16 ≤ i) → ∀ r ∈ [(8 * sW, 8), (8 * sArr 0, 64)],
      8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i := by
    intro i h6 hr
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl) <;> simp only [eW, eA] <;> omega
  refine WP.seq (WP.mono (setupHead_ok hs hp.rdi hZ (by omega) hp.hK hp.hN)
    fun t₁ ⟨h12, hcx, hsi, hbx, hW₁, hb₁, hf₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have in₁ : InScr B Z s.mem t₁.mem := InScr.of_frm hf₁ hsl
  refine WP.seq (WP.mono (loadArr_ok hs₁ (j := aN) (by decide) hZ (hp.srN.congrK in₁ k₁) hp.nl (by omega)
    (by omega) hsi hcx hbx) fun t₂ ⟨hv₂, ha₂, k₂⟩ => ?_)
  have hs₂ := hs₁.congr k₂.2.2
  have hdi₂ : t₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hp.rdi)
  refine WP.seq (WP.mono (WP.keep [.rdx, .rcx] (Q := fun t => t.gpr .rdx = 1 ∧
      t.gpr .rcx = BitVec.ofNat 64 0 ∧ t.mem = t₂.mem) (by xrun []) rfl)
    fun t₃ ⟨⟨hdx₃, hcx₃, hm₃⟩, k₃⟩ => ?_)
  have hH : Hdr t₃.mem B ((k + 7) / 8) (word s.mem B (8 * sMinv)) :=
    ⟨by rw [hm₃, ha₂.hslot (by decide)]; exact hW₁,
      by rw [hm₃, ha₂.hslot (by decide), hf₁.word_eq (hfw sMinv (by decide) (by decide)) (by omega)],
      fun j hj => by rw [hm₃, ha₂.hslot (by unfold sArr; omega)]; exact hb₁ j hj⟩
  have hs₃ := hs₂.congr k₃.2.2
  have h12₃ : t₃.gpr .r12 = BitVec.ofNat 64 ((k + 7) / 8) :=
    (k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12)
  have hdi₃ : t₃.gpr .rdi = B := (k₃.gpr (by decide)).trans hdi₂
  refine WP.seq (WP.mono (setWord_ok hs₃ hdi₃ hH hZ h12₃ (by omega) (by omega) (o := aOne) (by decide)
    (ri := .rcx) (by decide) (i := 0) (by omega) hcx₃) fun t₄ ⟨hone, ho₄, k₄⟩ => ?_)
  have hs₄ := hs₃.congr k₄.2.2
  have hdi₄ : t₄.gpr .rdi = B := (k₄.gpr (by decide)).trans hdi₃
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = t₄.mem.writeW (off B (8 * sMask)) (mask true)) (by
    xrun [State.ea, hdr, hdi₄, hdrOff, hs₄.st (d := 8 * sMask) (by omega)]
    exact congrArg _ (by decide)) rfl) fun t ⟨hm, k₅⟩ => ?_
  have ha₄ : Arrays B ((k + 7) / 8) [aOne] t₃.mem t₄.mem :=
    Arrays.of_outside (List.mem_singleton_self _) ho₄ (Nat.le_refl _) (Nat.le_refl _)
  have hn' : B.toNat + slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega
  have ho₅ : Outside B (8 * sMask) 8 t₄.mem t.mem := by rw [hm]; exact writeW_outside _ B _ (by omega)
  have kk : Keep mmRegs s t := ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by decide)
  refine ⟨word s.mem B (8 * sMinv), ⟨⟨hs₄.congr k₅.2.2, (k₅.gpr (by decide)).trans hdi₄,
      by rw [hm]; exact Hdr.store (ha₄.hdr hH) (i := sMask) (by decide) (by decide) _⟩,
    hZ, by omega, by omega, fun _ _ _ => rfl, InScr.refl _ _ _, rfl, rfl, ?_, ?_⟩,
    by rw [hm, word_writeW_self], fun i hi hsi => ?_,
    ((in₁.trans (InScr.of_arrays ha₂ hZ (by decide))).trans (by rw [hm₃]; exact InScr.refl _ _ _)).trans
      ((InScr.of_arrays ha₄ hZ (by decide)).trans (InScr.of_outside ho₅ (by omega))),
    kk.2.1, kk.2.2, kk⟩
  · rw [Outside.wv_arr ho₅ (by decide) hZ hn (by omega), ha₄.wv_of_not_mem (by decide) (by decide) hn', hm₃]
    exact hv₂
  · rw [Outside.wv_arr ho₅ (by decide) hZ hn (by omega), hone, hdx₃]; rfl
  · obtain ⟨h6, hr, h22⟩ := setupSlot_false i hi hsi
    rw [hm, hdrStore_hdr _ _ _ (by decide) hi (by rw [eM]; omega), ha₄.hslot hi, hm₃, ha₂.hslot hi,
      hf₁.word_eq (hfw i h6 hr) (by omega)]

end VG.Proof.Rsa.X86_64

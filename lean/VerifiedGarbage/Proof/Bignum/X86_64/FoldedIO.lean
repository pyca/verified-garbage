import VerifiedGarbage.Proof.Bignum.X86_64.PdMain
import VerifiedGarbage.Proof.Bignum.X86_64.WordIOStore
import VerifiedGarbage.Proof.Bignum.X86_64.Compare8

namespace VG.Proof.Bignum.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

def wordIn : List (Prog isa) :=
  [.block [.mov .rsi (.mem (hdr sIn)), .mov .rcx (.mem (hdr sK)), .mov .rbx (.mem (hdr (sArr aX)))], VG.Impl.Rsa.X86_64.WordIO.load]

theorem wordLoadArr_ok {s : State} {B : Addr} {Z k : Nat} {p : Addr} {bs : List Byte} {j : Nat} (hs : Scr s B Z)
    (hspan : InRegions (s.rd ++ s.wr) p k) (hj : j < 8) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hsrc : Src s B Z p bs) (hk : bs.length = k) (hk1 : 1 ≤ k)
    (hk' : k < 2 ^ 31) (hsi : s.gpr .rsi = p) (hcx : s.gpr .rcx = BitVec.ofNat 64 k)
    (hbx : s.gpr .rbx = off B (slot ((k + 7) / 8) j)) :
    WP isa VG.Impl.Rsa.X86_64.WordIO.load s fun t =>
      wv t.mem B (slot ((k + 7) / 8) j) ((k + 7) / 8) = Spec.Rsa.os2ip bs ∧
      Arrays B ((k + 7) / 8) [j] s.mem t.mem ∧ Keep [.rax, .rdx, .rbp, .r14] s t := by
  have := slot_le (w := (k + 7) / 8) hj
  refine WP.mono (WordIO.load_ok hs hsi hcx hbx hk hk1 hk' rfl (by omega) hspan
    (fun i hi => hsrc.val i (by omega)) (fun i hi => Or.inr (by have := hsrc.out i (by omega); omega)))
    fun t ⟨h1, h2, h3⟩ => ⟨h1, Arrays.of_outside (List.mem_singleton_self j) h2 (Nat.le_refl _) (by omega), h3⟩

theorem wordIn_ok {s : State} {B : Addr} {Z k : Nat} {ip : Addr} {xb : List Byte} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 9 ≤ k) (hk : k < 2 ^ 31)
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hIn : word s.mem B (8 * sIn) = ip)
    (hb : ∀ j < 8, word s.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j)) (hx : Src s B Z ip xb)
    (hxl : xb.length = k) (hspan : InRegions (s.rd ++ s.wr) ip k) :
    WP isa (seqs wordIn) s fun t => wv t.mem B (slot ((k + 7) / 8) aX) ((k + 7) / 8) = Spec.Rsa.os2ip xb ∧
      Arrays B ((k + 7) / 8) [aX] s.mem t.mem ∧ Keep [.rax, .rcx, .rdx, .rbx, .rsi, .rbp, .r14] s t := by
  have hn := hs.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 0 (show 31 < 32 by decide)
  have h0 := slot_le (w := (k + 7) / 8) (show 0 < 8 by decide)
  have eK : sK = 18 := rfl
  have eIn : sIn = 21 := rfl
  have eAX : sArr aX = 9 := rfl
  unfold wordIn
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .rbx] (Q := fun t => t.gpr .rsi = ip ∧
      t.gpr .rcx = BitVec.ofNat 64 k ∧ t.gpr .rbx = off B (slot ((k + 7) / 8) aX) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hs.ld (d := 8 * sIn) (by omega), hs.ld (d := 8 * sK) (by omega),
      hs.ld (d := 8 * sArr aX) (by omega), hIn, hK, hb aX (by decide)]) rfl)
    fun t₁ ⟨⟨hsi, hcx, hbx, hm₁⟩, k₁⟩ => ?_)
  rw [seqs_one]
  refine WP.mono (wordLoadArr_ok (hs.congr k₁.2.2) (by rw [k₁.2.1, k₁.2.2]; exact hspan) (by decide) hZ
    (hx.congrK (by rw [hm₁]; exact InScr.refl _ _ _) k₁) hxl (by omega) hk hsi hcx hbx)
    fun t ⟨hv, ha, k₂⟩ => ⟨hv, by rw [hm₁] at ha; exact ha, (k₁.trans k₂).mono (by decide)⟩

theorem wordSetup_ok {s : State} {B : Addr} {Z k : Nat} {op ep ip : Addr} {L : Nat} {eb xb : List Byte} {N R : Nat}
    (h : PdPre s B Z k op ep ip L eb xb N R) :
    WP isa (seqs (wordIn ++ restStepsWith VG.Impl.Rsa.X86_64.Compare8.code)) s fun t => ∃ minv,
      SetupOut t B Z ((k + 7) / 8) minv N (Spec.Rsa.os2ip xb) ∧ Frm B (pdAll ((k + 7) / 8)) s.mem t.mem ∧
      Keep mmRegs s t ∧ wv t.mem B (slot ((k + 7) / 8) aR2) ((k + 7) / 8) = R := by
  have hk1 := h.k1
  have hk2 := h.k2
  have hZ := h.z
  have hs := h.scr
  have hn := hs.nowrap
  have hn' : B.toNat + slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega
  -- The input.
  refine wp_seqs_append (by simp [wordIn]) (by simp [restStepsWith])
    (WP.mono (wordIn_ok hs h.rdi hZ (by omega) (by omega) h.hK h.hIn h.hb h.x h.xl h.inSpan) fun t₁ ⟨hX₁, ha₁, k₁⟩ => ?_)
  have f₁ : Frm B (pdAll ((k + 7) / 8)) s.mem t₁.mem := Frm.of_arrays ha₁ (by simp [pdAll])
  -- The mask, `-m⁻¹` and 1.
  refine WP.mono (setupRestWith_ok VG.Impl.Rsa.X86_64.Compare8.code @Compare8.code_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans h.rdi) hZ (by omega) (by omega)
      (by rw [ha₁.hslot (by decide)]; exact h.hW) (fun j hj => by rw [ha₁.hslot (by unfold sArr; omega)]; exact h.hb j hj)
      (by rw [ha₁.wv_of_not_mem (by decide) (by decide) hn']; exact h.n) hX₁ h.odd)
      fun t₂ ⟨minv, so, f₂', k₂⟩ => ⟨minv, so, f₁.trans (f₂'.mono (by simp [pdAll])), (k₁.trans k₂).mono (by decide), ?_⟩
  rw [f₂'.wv_eq (fun r hr => by
      have := hdr_lt_slot ((k + 7) / 8) aR2 (show 31 < 32 by decide)
      have := slot_sep (w := (k + 7) / 8) (show aR2 ≠ aOne by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [sMinv, sMask, sFn] at * <;> omega)
      (by have := slot_le (w := (k + 7) / 8) (show aR2 < 8 by decide); omega),
    ha₁.wv_of_not_mem (by decide) (by decide) hn']
  exact h.r

def wordOutStepsArr (j : Nat) : List (Prog isa) := [
  .block [.mov .rbx (.mem (hdr (sArr j))), .mov .rsi (.mem (hdr sOut)), .mov .rcx (.mem (hdr sK)),
    .mov .r15 (.mem (hdr sMask))],
  VG.Impl.Rsa.X86_64.WordIO.store,
  .block ([.mov .rax (.mem (hdr sMask)), .alu .and .rax (.imm 1)] ++ exit)]

theorem wordOutPhaseArr_ok {s : State} {B : Addr} {Z k : Nat} {minv : BitVec 64} {Y : Nat} {out : Addr} {c : Bool}
    {j : Nat} (hj : j < 8)
    (hg : Good s B Z ((k + 7) / 8) minv) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hY : wv s.mem B (slot ((k + 7) / 8) j) ((k + 7) / 8) = Y)
    (hO : word s.mem B (8 * sOut) = out) (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hM : word s.mem B (8 * sMask) = mask c)
    (hout : InRegions s.wr out k)
    (hsep : ∀ j < k, Z ≤ ofs B (out + BitVec.ofNat 64 j)) :
    WP isa (seqs (wordOutStepsArr j)) s fun t =>
      (List.range k).map (fun i => t.mem (out + BitVec.ofNat 64 i)) = Spec.Rsa.i2osp (if c then Y else 0) k ∧
      t.gpr .rax = BitVec.ofNat 64 c.toNat ∧
      (∀ i < 6, t.gpr (saved.getD i .rax) = word s.mem B (8 * i)) ∧
      (∀ x, (∀ j < k, x ≠ out + BitVec.ofNat 64 j) → t.mem x = s.mem x) ∧
      Keep mmRegs s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h0 := hdr_lt_slot ((k + 7) / 8) 0 (show 31 < 32 by decide)
  have h0' := slot_le (w := (k + 7) / 8) (show 0 < 8 by decide)
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  unfold wordOutStepsArr
  refine WP.seq (WP.mono (WP.keep [.rbx, .rsi, .rcx, .r15] (Q := fun t =>
      t.gpr .rbx = off B (slot ((k + 7) / 8) j) ∧ t.gpr .rsi = out ∧ t.gpr .rcx = BitVec.ofNat 64 k ∧
      t.gpr .r15 = mask c ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr j) (by unfold sArr; omega), hl sOut (by decide), hl sK (by decide),
      hl sMask (by decide), hg.hdr.harr j hj, hO, hK, hM]) rfl)
    fun t₁ ⟨⟨hbx, hsi, hcx, h15, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  refine WP.seq (WP.mono (WordIO.store_ok hs₁ hbx hsi hcx h15 hk1 hk' rfl
    (by have := slot_le (w := (k + 7) / 8) hj; omega)
    (by rw [k₁.2.2]; exact hout) hsep) fun t₂ ⟨hb₂, hf₂, hwr₂, hrd₂, k₂⟩ => ?_)
  rw [hm₁, hY] at hb₂
  have hw₂ : ∀ i < 32, word t₂.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    apply Mem.readW_congr
    intro b hb
    rw [hf₂ _ (scr_ne_out hsep (d := 8 * i) (i := b) (by omega) (by omega)), hm₁]
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off B (8 * i)) 8 := fun i hi => by
    rw [hrd₂, hwr₂, k₁.2.1, k₁.2.2]; exact hl i hi
  have hdi₂ : t₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hg.rdi)
  rw [exit_eq]
  refine WP.mono (WP.keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
      t.gpr .rax = BitVec.ofNat 64 c.toNat ∧ t.gpr .rbx = word s.mem B (8 * 0) ∧
      t.gpr .rbp = word s.mem B (8 * 1) ∧ t.gpr .r12 = word s.mem B (8 * 2) ∧
      t.gpr .r13 = word s.mem B (8 * 3) ∧ t.gpr .r14 = word s.mem B (8 * 4) ∧
      t.gpr .r15 = word s.mem B (8 * 5) ∧ t.mem = t₂.mem) (by
    simp only [List.cons_append, List.nil_append]
    xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ sMask (by decide), hw₂ sMask (by decide), hM, mask_and1,
      hl₂ 0 (by decide), hl₂ 1 (by decide), hl₂ 2 (by decide), hl₂ 3 (by decide), hl₂ 4 (by decide),
      hl₂ 5 (by decide), hw₂ 0 (by decide), hw₂ 1 (by decide), hw₂ 2 (by decide), hw₂ 3 (by decide),
      hw₂ 4 (by decide), hw₂ 5 (by decide)]) rfl)
    fun t ⟨⟨hax, h0, h1, h2, h3, h4, h5, hm⟩, k₃⟩ => ⟨by rw [hm]; exact hb₂, hax, ?_,
      fun x hx => by rw [hm, hf₂ x hx, hm₁], ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem wordOutPhase_ok {s : State} {B : Addr} {Z k : Nat} {minv : BitVec 64} {Y : Nat} {out : Addr} {c : Bool}
    (hg : Good s B Z ((k + 7) / 8) minv) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hY : wv s.mem B (slot ((k + 7) / 8) aY) ((k + 7) / 8) = Y)
    (hO : word s.mem B (8 * sOut) = out) (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hM : word s.mem B (8 * sMask) = mask c)
    (hout : InRegions s.wr out k)
    (hsep : ∀ j < k, Z ≤ ofs B (out + BitVec.ofNat 64 j)) :
    WP isa (seqs (wordOutStepsArr aY)) s fun t =>
      (List.range k).map (fun i => t.mem (out + BitVec.ofNat 64 i)) = Spec.Rsa.i2osp (if c then Y else 0) k ∧
      t.gpr .rax = BitVec.ofNat 64 c.toNat ∧
      (∀ i < 6, t.gpr (saved.getD i .rax) = word s.mem B (8 * i)) ∧
      (∀ x, (∀ j < k, x ≠ out + BitVec.ofNat 64 j) → t.mem x = s.mem x) ∧
      Keep mmRegs s t :=
  wordOutPhaseArr_ok (by decide) hg hZ hk1 hk' hY hO hK hM hout hsep


end VG.Proof.Bignum.X86_64

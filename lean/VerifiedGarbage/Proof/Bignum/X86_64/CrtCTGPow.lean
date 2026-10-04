import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.X86_64.CTR2

/-!
# RSA with the CRT on x86-64: `G = 2^E mod n` is constant time

`gPow` computes in `n`'s workspace, all public: the prime's length `w_X`,
hence `K`, `D` and the bits of `D` the loop branches on, are the same in
both runs (`gPow_ct`). Its loads through the prime's base (in a header slot)
are pinned by correctness, the bits of `D` from `gBit_ok`'s invariant.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- `n`'s layout. -/
abbrev GPub.L (p : GPub) : Lay := ⟨p.B, p.Z, p.w, p.minv⟩

/-- After the top `j` bits of `D` in `gPow`'s loop. -/
def GLoop (p : GPub) (j : Nat) (t : State) : Prop :=
  ∃ s₀, GInv s₀ p.B p.Z p.w p.minv p.N (gD p.w p.wx) (gD p.w p.wx).log2 j t ∧ slot p.w 8 ≤ p.Z ∧ 2 ≤ p.w ∧ p.w < 2
      ^ 30 ∧
    p.N % 2 = 1 ∧ 1 < p.N ∧ 1 ≤ p.wx ∧ p.wx ≤ p.w

/-- After the squaring of bit `j`. -/
def GB1 (q : GPub × Nat) (t : State) : Prop :=
  (Good t q.1.B q.1.Z q.1.w q.1.minv ∧ slot q.1.w 8 ≤ q.1.Z) ∧ 2 ≤ q.1.w ∧ q.1.w < 2 ^ 30 ∧ q.2 < (gD q.1.w
      q.1.wx).log2 + 1 ∧ (gD q.1.w q.1.wx).log2 < 62 ∧
    wv t.mem q.1.B (slot q.1.w Public.aY) q.1.w < wv t.mem q.1.B (slot q.1.w Public.aN) q.1.w ∧
    word t.mem q.1.B (8 * sD) = BitVec.ofNat 64 (gD q.1.w q.1.wx) ∧
    word t.mem q.1.B (8 * Public.sCnt) = BitVec.ofNat 64 (2 ^ ((gD q.1.w q.1.wx).log2 - q.2))

/-- After the test of bit `j`. -/
def GB2 (q : GPub × Nat) (t : State) : Prop :=
  (Good t q.1.B q.1.Z q.1.w q.1.minv ∧ slot q.1.w 8 ≤ q.1.Z) ∧ 2 ≤ q.1.w ∧ q.1.w < 2 ^ 30 ∧
    wv t.mem q.1.B (slot q.1.w Public.aY) q.1.w < wv t.mem q.1.B (slot q.1.w Public.aN) q.1.w ∧
    t.zf = some (decide ((gD q.1.w q.1.wx) / 2 ^ ((gD q.1.w q.1.wx).log2 - q.2) % 2 = 0))

theorem exec_seqs_split {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ []) {s s' : State} {t : List Leak}
    (e : Exec isa (seqs (a ++ b)) s t s') : Exec isa (.seq (seqs a) (seqs b)) s t s' := by
  induction a generalizing s t with
  | nil => exact absurd rfl ha
  | cons c a ih =>
    cases a with
    | nil =>
      obtain ⟨d, rest, rfl⟩ := List.exists_cons_of_ne_nil hb
      exact e
    | cons d rest =>
      change Exec isa (.seq c (seqs (d :: rest ++ b))) s t s' at e
      change Exec isa (.seq (.seq c (seqs (d :: rest))) (seqs b)) s t s'
      obtain ⟨t₁, t₂, s₁, rfl, e₁, e₂⟩ : ∃ t₁ t₂ s₁, t = t₁ ++ t₂ ∧ Exec isa c s t₁ s₁ ∧
          Exec isa (seqs (d :: rest ++ b)) s₁ t₂ s' := by
        cases e with
        | seq e₁ e₂ => exact ⟨_, _, _, rfl, e₁, e₂⟩
      obtain ⟨u₁, u₂, s₂, rfl, f₁, f₂⟩ : ∃ u₁ u₂ s₂, t₂ = u₁ ++ u₂ ∧ Exec isa (seqs (d :: rest)) s₁ u₁ s₂ ∧
          Exec isa (seqs b) s₂ u₂ s' := by
        cases ih (by simp) e₂ with
        | seq f₁ f₂ => exact ⟨_, _, _, rfl, f₁, f₂⟩
      rw [← List.append_assoc]
      exact .seq (.seq e₁ f₁) f₂

/-- A sequence in two parts leaks as their sequence. -/
theorem RelCT.seqs_split {P Q : State → State → Prop} {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ [])
    (h : RelCT isa P (.seq (seqs a) (seqs b)) Q) : RelCT isa P (seqs (a ++ b)) Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (exec_seqs_split ha hb e₁) (exec_seqs_split ha hb e₂)

theorem pins_rdiB {α : Type} {Φ : α → State → Prop} (B : α → Addr) (h : ∀ a s, Φ a s → s.gpr .rdi = B a) :
    Pins Φ [.rdi] :=
  pins_of (fun a _ => B a) fun a s hs r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h a s hs

/-- One bit of `D`: the squaring, the test and the doubling. -/
theorem gBody_ct (M : Mont) : RelCT isa (Two fun (q : GPub × Nat) s => q.2 < (gD q.1.w q.1.wx).log2 + 1 ∧ GLoop q.1
    q.2 s)
    (seqs (gBody M.mm)) fun _ _ => True := by
  simp only [gBody, seqs]
  -- The squaring.
  refine RelCT.seq (two_post (Ψ := GB1) (two_map (fun q => q.1.L.ws)
    (fun q s ⟨_, _, hI, hZ, _⟩ => ⟨q.1.minv, hI.good, hZ⟩) (M.ct (by unfold MmUse; decide))) ?_) ?_
  · rintro q s ⟨hj, s₀, hI, hZ, hw, hw30, -, -, hwx, hwx'⟩
    obtain ⟨hD0, hD1, -⟩ := gD_bounds hwx hwx' hw30
    have hL : (gD q.1.w q.1.wx).log2 < 62 := (Nat.log2_lt (by omega)).mpr hD1
    have hc2 : 2 ^ ((gD q.1.w q.1.wx).log2 + 1 - q.2) / 2 = 2 ^ ((gD q.1.w q.1.wx).log2 - q.2) := by
      rw [show (gD q.1.w q.1.wx).log2 + 1 - q.2 = ((gD q.1.w q.1.wx).log2 - q.2) + 1 by omega, Nat.pow_succ,
        Nat.mul_div_cancel _ (by decide)]
    refine WP.mono (mmN_ok M (o := Public.aY) (a := Public.aY) (b := Public.aY) hI.good hZ hw (by omega)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hI.n hI.inv
      hI.ylt) fun t₁ ⟨hg₁, hn₁, _, hlt₁, _, ha₁, _⟩ => ⟨⟨hg₁, hZ⟩, hw, hw30, hj, hL, by rw [hn₁]; exact hlt₁,
        by rw [ha₁.hslot (by decide)]; exact hI.d, by rw [ha₁.hslot (by decide), hI.c, hc2]⟩
  -- The bit, into ZF.
  refine RelCT.seq (two_piece (Ψ := GB2) [.rdi] (pins_rdiB (fun q => q.1.B) fun _ _ h => h.1.1.rdi)
    (by taint_decide) ?_) ?_
  · rintro q t₁ ⟨hg₁, hw, hw30, hj, hL, hlt, hd, hc⟩
    have hZ := hg₁.2
    have hl₁ : ∀ i < 32, InRegions (t₁.rd ++ t₁.wr) (off q.1.B (8 * i)) 8 := fun i hi =>
      hg₁.1.scr.ld (by have := hdr_lt_slot q.1.w 8 hi; omega)
    refine WP.mono (WP.keep [.rax] (Q := fun t₂ =>
        t₂.zf = some (decide ((gD q.1.w q.1.wx) / 2 ^ ((gD q.1.w q.1.wx).log2 - q.2) % 2 = 0)) ∧ t₂.mem = t₁.mem) (by
      xrun [State.ea, hdr, hg₁.1.rdi, hdrOff, hl₁ sD (by decide), hl₁ Public.sCnt (by decide), hd, hc,
        and_pow_beq (gD q.1.w q.1.wx) ((gD q.1.w q.1.wx).log2 - q.2) (by omega)]) rfl)
      fun t₂ ⟨⟨hz, hm⟩, k⟩ => ⟨⟨⟨hg₁.1.scr.congr k.2.2, (k.gpr (by decide)).trans hg₁.1.rdi, hm ▸ hg₁.1.hdr⟩,
        hg₁.2⟩, hw, hw30, by rw [hm]; exact hlt, hz⟩
  -- Doubled if it is set.
  refine RelCT.seq (R := Two fun (q : GPub × Nat) t => (Good t q.1.B q.1.Z q.1.w q.1.minv ∧ slot q.1.w 8 ≤ q.1.Z))
    (two_ite (fun q s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2.2.2.2, h₂.2.2.2.2]) ?_ ?_) ?_
  · refine two_post (two_map (fun q => q.1.L) (fun _ _ h => h.1.1)
      (double_ct (by decide) (by decide) (by decide) (by decide) (by taint_decide))) fun q t h => ?_
    obtain ⟨⟨hg, hw, hw30, hlt, -⟩, -⟩ := h
    exact WP.mono (double_ok hg.1.scr hg.1.rdi hg.1.hdr hg.2 hw (by omega) (mo := Public.aN) (acc := Public.aAcc)
      (tmp := Public.aTmp) (o := Public.aY) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hlt) fun t' ⟨_, ha, k⟩ =>
        ⟨⟨hg.1.scr.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, ha.hdr hg.1.hdr⟩, hg.2⟩
  · exact RelCT.block_nil fun _ _ hp => two_mono (fun _ _ h => h.1.1) hp
  -- The next bit.
  exact two_taint [.rdi] (pins_rdiB (fun q => q.1.B) fun _ _ h => h.1.rdi) (by taint_decide)

/-- The bits of `D`. -/
theorem gLoop_ct (M : Mont) : RelCT isa (Two fun p s => 0 < (gD p.w p.wx).log2 + 1 ∧ GLoop p 0 s)
    (.loop (seqs (gBody M.mm)) .ne) (Two fun (_ : GPub) (_ : State) => True) :=
  two_loop (Φ := GLoop) (fun p => (gD p.w p.wx).log2 + 1) (gBody_ct M)
    fun p j s hj ⟨s₀, hI, hZ, hw, hw30, hodd, hN1, hwx, hwx'⟩ => by
      obtain ⟨hD0, hD1, -⟩ := gD_bounds hwx hwx' hw30
      have hL : (gD p.w p.wx).log2 < 62 := (Nat.log2_lt (by omega)).mpr hD1
      exact WP.mono (gBit_ok M hZ hw (by omega) (VG.Proof.Bignum.coprime_pow2 hodd _) (by omega) (by omega) hj hI)
        fun s' ⟨hz, hI'⟩ => ⟨eval_ne_count hj hz, fun _ => ⟨s₀, hI', hZ, hw, hw30, hodd, hN1, hwx, hwx'⟩,
          fun _ => trivial⟩

/-- After the load of the prime's base. -/
def GA (sl : Nat) (p : GPub) (t : State) : Prop :=
  ∃ s, GPre sl p s ∧ t.mem = s.mem ∧ Keep [.rax] s t ∧ t.gpr .rax = p.Bx

/-- After the loads of `w_X` and `w`. -/
def GBk (p : GPub) (t : State) : Prop :=
  t.gpr .rdi = p.B ∧ t.gpr .rax = BitVec.ofNat 64 p.wx ∧ t.gpr .r12 = BitVec.ofNat 64 p.w ∧
    t.gpr .rcx = BitVec.ofNat 64 0

/-- After `gHead`: `D`. -/
def GHd (sl : Nat) (p : GPub) (t : State) : Prop :=
  ∃ s, GPre sl p s ∧ t.gpr .rax = BitVec.ofNat 64 (gD p.w p.wx) ∧
    t.mem = s.mem.writeW (off p.B (8 * sD)) (BitVec.ofNat 64 (gD p.w p.wx)) ∧ Keep [.rax, .rcx, .r12] s t

/-- After `D`'s top bit into `sCnt`. -/
def GTop (sl : Nat) (p : GPub) (t : State) : Prop :=
  ∃ s, GPre sl p s ∧ Good t p.B p.Z p.w p.minv ∧
    t.mem = (s.mem.writeW (off p.B (8 * sD)) (BitVec.ofNat 64 (gD p.w p.wx))).writeW (off p.B (8 * Public.sCnt))
      (BitVec.ofNat 64 (2 ^ (gD p.w p.wx).log2)) ∧ Keep mmRegs s t

/-- `gHead`, given that the taint analysis checks the load of the prime's
base (`by taint_decide` for a given `sl`). -/
theorem gHead_ct {sl : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rax (.mem (hdr sl))]) hc).isSome = true) :
    RelCT isa (Two (GPre sl)) (seqs (gHead sl)) fun _ _ => True := by
  simp only [gHead, seqs]
  refine RelCT.seq (RelCT.block_append (l₁ := ([.mov .rax (.mem (hdr sl))] : List Instr))
    (RelCT.seq (two_piece (Ψ := GA sl) [.rdi] (pins_rdiB (fun p => p.B) fun _ _ h => h.1.rdi) hT ?_)
      (two_piece (Ψ := GBk) [.rdi, .rax] (pins_of (fun p r => if r = .rdi then p.B else p.Bx) fun p s h r hr => ?_)
        (by taint_decide) ?_)))
    (two_taint [.rdi, .rax, .r12, .rcx] (pins_of (fun p r => if r = .rdi then p.B else if r = .rax then
      BitVec.ofNat 64 p.wx else if r = .r12 then BitVec.ofNat 64 p.w else BitVec.ofNat 64 0) fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2.1
        · exact h.2.2.2) (by taint_decide))
  · intro p s h
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * i)) 8 := fun i hi =>
      h.1.scr.ld (by have := hdr_lt_slot p.w 8 hi; have := h.2.1; omega)
    exact WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = p.Bx ∧ t.mem = s.mem)
      (by xrun [State.ea, hdr, h.1.rdi, hdrOff, hl sl h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1]) rfl)
      fun t ⟨⟨h1, h2⟩, k⟩ => ⟨s, h, h2, k, h1⟩
  · obtain ⟨σ, hσ, -, k, hax⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (k.gpr (by decide)).trans hσ.1.rdi
    · exact hax
  · rintro p t ⟨s, ⟨hg, hZ, _, _, _, _, _, _, _, _, _, _, hXw, hXr, _⟩, hm, k, hax⟩
    have hdi : t.gpr .rdi = p.B := (k.gpr (by decide)).trans hg.rdi
    have hXr' : InRegions (t.rd ++ t.wr) (off p.Bx (8 * sW)) 8 := by rw [k.2.1, k.2.2]; exact hXr
    have hW : InRegions (t.rd ++ t.wr) (off p.B (8 * sW)) 8 := by
      rw [k.2.1, k.2.2]; exact hg.scr.ld (by have := hdr_lt_slot p.w 8 (show sW < 32 by decide); omega)
    have hXw' : word t.mem p.Bx (8 * sW) = BitVec.ofNat 64 p.wx := by rw [hm]; exact hXw
    have hw' : word t.mem p.B (8 * sW) = BitVec.ofNat 64 p.w := by rw [hm]; exact hg.hdr.hw
    exact WP.mono (WP.keep [.rax, .r12, .rcx] (Q := fun t' => t'.gpr .rax = BitVec.ofNat 64 p.wx ∧
        t'.gpr .r12 = BitVec.ofNat 64 p.w ∧ t'.gpr .rcx = BitVec.ofNat 64 0)
      (by xrun [State.ea, hdr, ws, hdi, hax, hdrOff, hXr', hXw', hW, hw']) rfl)
      fun t' ⟨h', k'⟩ => ⟨(k'.gpr (by decide)).trans hdi, h'⟩

/-- `D`'s top bit into `sCnt`. -/
theorem gTop_ct (sl : Nat) : RelCT isa (Two (GHd sl)) (.seq topBit (.block [.store (hdr Public.sCnt) .rdx]))
    (Two (GTop sl)) := by
  refine two_piece [.rax, .rdi] (pins_of (fun p r => if r = .rax then BitVec.ofNat 64 (gD p.w p.wx) else p.B)
    fun p s h r hr => ?_) (by taint_decide) ?_
  · obtain ⟨σ, hσ, hax, -, k⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hax
    · exact (k.gpr (by decide)).trans hσ.1.rdi
  rintro p t₁ ⟨s, h, hax₁, hm₁, k₁⟩
  obtain ⟨hg, hZ, hw, hw30, _, _, _, _, _, _, _, _, _, _, hwx, hwx'⟩ := id h
  obtain ⟨hD0, hD1, -⟩ := gD_bounds hwx hwx' hw30
  have hs₁ := hg.scr.congr k₁.2.2
  have hdi₁ : t₁.gpr .rdi = p.B := (k₁.gpr (by decide)).trans hg.rdi
  refine WP.seq (WP.mono (topBit_ok hax₁ hD0 (by omega)) fun t₂ ⟨hdx₂, _, hm₂, k₂⟩ => ?_)
  have hs₂ := hs₁.congr k₂.2.2
  have hdi₂ : t₂.gpr .rdi = p.B := (k₂.gpr (by decide)).trans hdi₁
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = t₂.mem.writeW (off p.B (8 * Public.sCnt))
      (BitVec.ofNat 64 (2 ^ (gD p.w p.wx).log2))) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hs₂.st (show 8 * Public.sCnt + 8 ≤ p.Z by
      have := hdr_lt_slot p.w 8 (show Public.sCnt < 32 by decide); omega), hdx₂]) rfl) fun t₃ ⟨hm₃, k₃⟩ => ?_
  have hm₃' : t₃.mem = (s.mem.writeW (off p.B (8 * sD)) (BitVec.ofNat 64 (gD p.w p.wx))).writeW (off p.B (8 *
      Public.sCnt))
      (BitVec.ofNat 64 (2 ^ (gD p.w p.wx).log2)) := by rw [hm₃, hm₂, hm₁]
  exact ⟨s, h,
    ⟨hs₂.congr k₃.2.2, (k₃.gpr (by decide)).trans hdi₂, by
      rw [hm₃']; exact Hdr.store (Hdr.store hg.hdr (by decide) (by decide) _) (by decide) (by decide) _⟩,
    hm₃', ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- `Y := R`: the loop's start. -/
theorem gStart_ok (M : Mont) {sl : Nat} {p : GPub} {t : State} (h : GTop sl p t) :
    WP isa (M.mm Public.aY Public.aR2 Public.aOne) t fun t' => 0 < (gD p.w p.wx).log2 + 1 ∧ GLoop p 0 t' := by
  obtain ⟨s, ⟨hg, hZ, hw, hw30, hn, hinv, hodd, hN1, hr2', hone, _, _, _, _, hwx, hwx'⟩, hg₃, hm₃', k₃⟩ := h
  have hnw := hg.scr.nowrap
  have hn' : p.B.toNat + slot p.w 8 ≤ 2 ^ 64 := by omega
  have hR : Nat.Coprime (2 ^ (64 * p.w)) p.N := VG.Proof.Bignum.coprime_pow2 hodd _
  obtain ⟨hD0, hD1, -⟩ := gD_bounds hwx hwx' hw30
  have hwv₃ : ∀ j < 8, wv t.mem p.B (slot p.w j) p.w = wv s.mem p.B (slot p.w j) p.w := fun j hj => by
    rw [hm₃', hdrStore_wv _ _ _ (by decide) hj hn', hdrStore_wv _ _ _ (by decide) hj hn']
  refine WP.mono (mmN_ok M (N := p.N) (o := Public.aY) (a := Public.aR2) (b := Public.aOne) hg₃ hZ hw (by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((hwv₃ Public.aN (by decide)).trans hn)
    (by rw [hm₃', hdrStore_word _ _ _ (by decide) (by decide) hn', hdrStore_word _ _ _ (by decide) (by decide) hn'];
        exact hinv)
    (by rw [hwv₃ Public.aOne (by decide), hone]; exact hN1))
    fun t₄ ⟨hg₄, hn₄, hinv₄, hlt₄, hm₄, ha₄, k₄⟩ => ⟨by omega, s, ?_, hZ, hw, hw30, hodd, hN1, hwx, hwx'⟩
  rw [hwv₃ Public.aR2 (by decide), hwv₃ Public.aOne (by decide), hone, Nat.mul_one] at hm₄
  have hY₄ : wv t₄.mem p.B (slot p.w Public.aY) p.w % p.N =
      2 ^ ((gD p.w p.wx) / 2 ^ ((gD p.w p.wx).log2 + 1 - 0)) * 2 ^ (64 * p.w) % p.N := by
    rw [Nat.sub_zero, Nat.div_eq_of_lt Nat.lt_log2_self, Nat.pow_zero, Nat.one_mul]
    apply VG.Proof.Bignum.mont_cancel hR
    rw [hm₄, hr2']
  have hfr₄ : Frm p.B (gRanges p.w) s.mem t₄.mem := by
    have o1 := writeW_outside s.mem p.B (BitVec.ofNat 64 (gD p.w p.wx)) (d := 8 * sD) (by unfold sD sFn; omega)
    have o2 := writeW_outside (s.mem.writeW (off p.B (8 * sD)) (BitVec.ofNat 64 (gD p.w p.wx))) p.B
      (BitVec.ofNat 64 (2 ^ (gD p.w p.wx).log2)) (d := 8 * Public.sCnt) (by unfold Public.sCnt sFn; omega)
    rw [← hm₃'] at o2
    exact ((Frm.of_outside o1 (by simp [gRanges])).trans (Frm.of_outside o2 (by simp [gRanges]))).trans
      (Frm.of_arrays ha₄ (by simp [gRanges]))
  exact ⟨hg₄, hn₄, hinv₄, hlt₄, hY₄,
    by rw [ha₄.hslot (by decide), hm₃', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self],
    by rw [ha₄.hslot (by decide), hm₃', word_writeW_self, Nat.sub_zero, Nat.pow_succ,
      Nat.mul_div_cancel _ (by decide)],
    hfr₄, (k₃.trans k₄).mono (by decide)⟩

/-- `gPow sl`, given that the taint analysis checks the load of the
prime's base. -/
theorem gPow_ct_of {M : Mont} {sl : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rax (.mem (hdr sl))]) hc).isSome = true) :
    GPowCT M sl := by
  unfold GPowCT
  rw [gPow_eq]
  refine RelCT.seqs_split (by simp [gHead]) (by simp) (RelCT.seq (two_post (Ψ := GHd sl) (gHead_ct hT)
    fun p s h => ?_) ?_)
  · obtain ⟨hg, hZ, hw, hw30, _, _, _, _, _, _, hsl, hX, hXw, hXr, hwx, hwx'⟩ := id h
    exact WP.mono (gHead_ok hg hZ hw hw30 hsl hX hXw hXr hwx hwx') fun t ⟨h1, h2, h3⟩ => ⟨s, h, h1, h2, h3⟩
  refine RelCT.assoc (RelCT.seq (gTop_ct sl) (RelCT.seq (two_post (two_map (fun p => p.L.ws)
    (fun p s h => ?_) (M.ct (by unfold MmUse; decide))) fun p s h => gStart_ok M h)
    ((gLoop_ct M).mono (fun _ _ h => h) fun _ _ _ => trivial)))
  obtain ⟨_, ⟨_, hZ, _⟩, hg, _⟩ := h
  exact ⟨p.minv, hg, hZ⟩

theorem gPow_ct_P (M : Mont) : GPowCT M sWsP := gPow_ct_of (by taint_decide)

theorem gPow_ct_Q (M : Mont) : GPowCT M sWsQ := gPow_ct_of (by taint_decide)

end VG.Proof.Bignum.X86_64

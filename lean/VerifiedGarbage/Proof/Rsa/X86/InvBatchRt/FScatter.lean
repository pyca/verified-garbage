module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.FBatch
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Red

/-! # The fused batches on i686: interleaving and back

`scatterLoop_ok`: `K` words from `W + S` into byte `x` of the elements from `W + D`;
`gatherLoop_ok`: the other way.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt.F

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86.R2Words

/-- `m'` agrees with `m` but at byte `x` of the first `K` elements from `D`. -/
def SlotWr (W : Addr) (D sz x K : Nat) (m m' : Mem) : Prop :=
  ∀ y, (∀ j < K, ofs W y < D + x + sz * j ∨ D + x + sz * j + 4 ≤ ofs W y) → m' y = m y

theorem SlotWr.w32 {W : Addr} {D sz x K : Nat} {m m' : Mem} (h : SlotWr W D sz x K m m') {d : Nat}
    (hd : ∀ j < K, d + 4 ≤ D + x + sz * j ∨ D + x + sz * j + 4 ≤ d) (hd' : d + 4 ≤ 2 ^ 64) :
    VG.Proof.Mont.w32 m' W d = VG.Proof.Mont.w32 m W d := by
  unfold VG.Proof.Mont.w32
  congr 1
  refine (Mem.readW_congr fun i hi => ?_).symm
  have hi' : i < 4 := by simpa using hi
  have e := ofs_off W (d := d) (i := i) (by omega_using [hd', hi])
  exact (h _ fun j hj => by rw [e]; have := hd j hj; omega_using [hi, this]).symm

/-- As a row's writes: the elements after the scratch one at `D - sz`. -/
theorem SlotWr.row {W : Addr} {A0 sz x n : Nat} {m m' : Mem} (h : SlotWr W (A0 + sz) sz x (n + 1) m m') :
    RowWr W A0 sz x n m m' := fun y hy _ => h y fun j hj => by
  have := hy (j + 1) (by omega_using [hj]); rw [Nat.mul_succ] at this; omega_using [this]

/-- The scatter's loop. -/
theorem scatterLoop_ok {s : State} {W : Addr} {bytes S D sz x K : Nat} (ws : Ws s W bytes)
    (hK : 0 < K) (hx : x + 4 ≤ sz) (hD : D + sz * K ≤ bytes) (hS : S + 4 * K ≤ bytes)
    (sep : S + 4 * K ≤ D ∨ D + sz * K ≤ S)
    (pb : PtrAt s W .ebp S) (pe : PtrAt s W .esi D) (pc : (s.gpr .ecx).toNat = K) :
    WP isa (scatterLoop sz x) s fun t =>
      SlotWr W D sz x K s.mem t.mem ∧
      (∀ w < K, VG.Proof.Mont.w32 t.mem W (D + x + sz * w) = VG.Proof.Mont.w32 s.mem W (S + 4 * w)) ∧
      Keeps [.eax, .ecx, .ebp, .esi] s t := by
  have nw := ws.nowrap
  have mK := Nat.mul_le_mul_left sz (show 0 ≤ K from Nat.zero_le _)
  refine WP.loop (M := isa) (fun rem u => ∃ k, k + rem = K ∧ 0 < rem ∧ Ws u W bytes ∧ PtrAt u W .ebp (S + 4 * k) ∧
      PtrAt u W .esi (D + sz * k) ∧ (u.gpr .ecx).toNat = K - k ∧ Keeps [.eax, .ecx, .ebp, .esi] s u ∧
      SlotWr W D sz x K s.mem u.mem ∧
      (∀ w < k, VG.Proof.Mont.w32 u.mem W (D + x + sz * w) = VG.Proof.Mont.w32 s.mem W (S + 4 * w))) ?_ K s
    ⟨0, by omega_using [], hK, ws, by simpa using pb, by simpa using pe, by simpa using pc, Keeps.refl _ _,
      fun _ _ => rfl, fun w hw => absurd hw (by omega_using [])⟩
  rintro rem u ⟨k, hk, hr, wsu, pbu, peu, pcu, Ku, Fu, Vu⟩
  have mk := Nat.mul_le_mul_left sz (show k + 1 ≤ K by omega_using [hk, hr])
  rw [Nat.mul_succ] at mk
  have sepk : ∀ j < K, D + x + sz * j + 4 ≤ S + 4 * k ∨ S + 4 * k + 4 ≤ D + x + sz * j := fun j hj => by
    have := Nat.mul_le_mul_left sz (show j + 1 ≤ K by omega_using [hj]); rw [Nat.mul_succ] at this; omega_using [hK, hx, hD, hS, sep, pc, nw, mK, hk, hr, pcu, mk, hj, this]
  obtain ⟨hb, aB, rB⟩ := ptrRead wsu pbu (d := 0) (by omega_using [hS, hk, hr])
  have hesi := ptr_eq peu
  have aE := addr_off W (x := D + sz * k) (d := x) (by omega_using [hx, hD, nw, mk])
  have wE := ws_write wsu (y := D + sz * k + x) (n := 4) (by omega_using [hx, hD, mk])
  have src : u.mem.readW (off W (S + 4 * k + 0)) 32 = s.mem.readW (off W (S + 4 * k)) 32 := by
    rw [Nat.add_zero]; exact BitVec.eq_of_toNat_eq (Fu.w32 (fun j hj => (sepk j hj).symm) (by omega_using [hS, nw, hk]))
  refine WP.mono (WP.keeps [.eax, .ecx, .ebp, .esi] (Q := fun v =>
      (v.gpr .ebp).toNat = (W.toNat + (S + 4 * (k + 1))) % 2 ^ 32 ∧
      (v.gpr .esi).toNat = (W.toNat + (D + sz * (k + 1))) % 2 ^ 32 ∧
      (v.gpr .ecx).toNat = K - (k + 1) ∧ v.zf = some (decide (K - (k + 1) = 0)) ∧
      v.mem = u.mem.writeW (off W (D + sz * k + x)) (s.mem.readW (off W (S + 4 * k)) 32)) ?_ rfl)
    fun v ⟨⟨e1, e2, e3, z, mv⟩, kv⟩ => ?_
  · xrun [hb, aB, rB, hesi, aE, wE, src]
    have hc := (u.gpr .ecx).isLt
    have hW := W.isLt
    have l4 : (4 : BitVec 32).toNat = 4 := rfl
    have l1 : (1 : BitVec 32).toNat = 1 := rfl
    have l0 : (0 : BitVec 32).toNat = 0 := rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [BitVec.toNat_add, BitVec.toNat_ofNat, l4]; omega_using []
    · simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; rw [Nat.mul_succ]; omega_using []
    · simp only [BitVec.toNat_sub, l1]; omega_using [hK, hx, hD, hS, sep, pc, nw, mK, hk, hr, pcu, mk, hc]
    · rw [Bool.eq_iff_iff]
      simp only [beq_iff_eq, decide_eq_true_eq, BitVec.toNat_eq, BitVec.toNat_sub, l1, l0]
      omega_using [hK, hx, hD, hS, sep, pc, nw, mK, hk, hr, pcu, mk, hc]
  -- The invariant.
  have Fv : SlotWr W D sz x K s.mem v.mem := fun y hy => by
    rw [mv, writeW32_outside _ _ _ (by omega_using [hK, hx, hD, hS, sep, pc, nw, mK, hk, hr, pcu, mk, e1, e2, e3]) y (by have := hy k (by omega_using [hK, hx, hD, hS, sep, pc, nw, mK, hk, hr, pcu, mk, e1, e2, e3]); omega_using [this])]; exact Fu y hy
  have Vv : ∀ w < k + 1, VG.Proof.Mont.w32 v.mem W (D + x + sz * w) = VG.Proof.Mont.w32 s.mem W (S + 4 * w) :=
    fun w hw => by
      rw [mv]
      rcases Nat.lt_or_ge w k with hw' | hw'
      · have := Nat.mul_le_mul_left sz (show w + 1 ≤ k by omega_using [hw']); rw [Nat.mul_succ] at this
        rw [w32_write_ne (size := bytes) nw (by omega_using [hx, hD, hS, sep, nw, mK, hk, pcu, mk, e1, e2, e3, hw, hw', this]) (by omega_using [hx, hD, mk, this]) (.inl (by omega_using [hx, hD, sep, mK, hk, pcu, mk, e1, e2, e3, hw, hw', this]))]; exact Vu w hw'
      · have : w = k := by omega_using [hw, hw']
        subst this
        rw [show D + x + sz * w = D + sz * w + x by omega_using [], w32_write_self]
  have Kv := Ku.trans kv
  by_cases last : k + 1 = K
  · left
    refine ⟨by change v.zf.map (!·) = some false; rw [z, show K - (k + 1) = 0 by omega_using [hK, hD, hS, sep, pc, mK, hk, pcu, mk, e1, e2, e3, last]]; rfl, Fv,
      fun w hw => Vv w (by omega_using [last, hw]), Kv⟩
  · right
    refine ⟨by change v.zf.map (!·) = some true; rw [z, decide_eq_false (by omega_using [hK, hx, hD, hS, sep, pc, nw, mK, hk, hr, pcu, mk, e1, e2, e3, last])]; rfl,
      rem - 1, by omega_using [hr], k + 1, by omega_using [hK, hD, hS, sep, pc, mK, hk, hr, pcu, mk, e1, e2, e3, last], by omega_using [hK, hD, hS, sep, pc, mK, hk, hr, pcu, mk, e1, e2, e3, last], wsu.of_keeps kv, e1, e2, by omega_using [hK, hD, hS, sep, pc, mK, hk, pcu, mk, e1, e2, e3, last], Kv, Fv, Vv⟩

/-- The gather's loop: byte `x` of the first `K` elements from `W + D` into `K` words at `W + S`. -/
theorem gatherLoop_ok {s : State} {W : Addr} {bytes S D sz x K : Nat} (ws : Ws s W bytes)
    (hK : 0 < K) (hx : x + 4 ≤ sz) (hD : D + sz * K ≤ bytes) (hS : S + 4 * K ≤ bytes)
    (sep : S + 4 * K ≤ D ∨ D + sz * K ≤ S)
    (pb : PtrAt s W .ebp S) (pe : PtrAt s W .esi D) (pc : (s.gpr .ecx).toNat = K) :
    WP isa (gatherLoop sz x) s fun t =>
      Outside W S (4 * K) s.mem t.mem ∧
      (∀ w < K, VG.Proof.Mont.w32 t.mem W (S + 4 * w) = VG.Proof.Mont.w32 s.mem W (D + x + sz * w)) ∧
      Keeps [.eax, .ecx, .ebp, .esi] s t := by
  have nw := ws.nowrap
  refine WP.loop (M := isa) (fun rem u => ∃ k, k + rem = K ∧ 0 < rem ∧ Ws u W bytes ∧ PtrAt u W .ebp (S + 4 * k) ∧
      PtrAt u W .esi (D + sz * k) ∧ (u.gpr .ecx).toNat = K - k ∧ Keeps [.eax, .ecx, .ebp, .esi] s u ∧
      Outside W S (4 * K) s.mem u.mem ∧
      (∀ w < k, VG.Proof.Mont.w32 u.mem W (S + 4 * w) = VG.Proof.Mont.w32 s.mem W (D + x + sz * w))) ?_ K s
    ⟨0, by omega_using [], hK, ws, by simpa using pb, by simpa using pe, by simpa using pc, Keeps.refl _ _,
      Outside.refl _ _ _ _, fun w hw => absurd hw (by omega_using [])⟩
  rintro rem u ⟨k, hk, hr, wsu, pbu, peu, pcu, Ku, Fu, Vu⟩
  have mk := Nat.mul_le_mul_left sz (show k + 1 ≤ K by omega_using [hk, hr])
  rw [Nat.mul_succ] at mk
  obtain ⟨hesi, aE, rE⟩ := ptrRead wsu peu (d := x) (by omega_using [hx, hD, mk])
  have hb := ptr_eq pbu
  have aB := addr_off W (x := S + 4 * k) (d := 0) (by omega_using [hS, nw, hk, hr])
  have wB := ws_write wsu (y := S + 4 * k + 0) (n := 4) (by omega_using [hS, hk, hr])
  have src : u.mem.readW (off W (D + sz * k + x)) 32 = s.mem.readW (off W (D + x + sz * k)) 32 := by
    rw [show D + sz * k + x = D + x + sz * k by omega_using []]
    exact BitVec.eq_of_toNat_eq (Fu.w32 (by omega_using [hx, sep, mk]) (by omega_using [hx, hD, nw, mk]))
  refine WP.mono (WP.keeps [.eax, .ecx, .ebp, .esi] (Q := fun v =>
      (v.gpr .ebp).toNat = (W.toNat + (S + 4 * (k + 1))) % 2 ^ 32 ∧
      (v.gpr .esi).toNat = (W.toNat + (D + sz * (k + 1))) % 2 ^ 32 ∧
      (v.gpr .ecx).toNat = K - (k + 1) ∧ v.zf = some (decide (K - (k + 1) = 0)) ∧
      v.mem = u.mem.writeW (off W (S + 4 * k + 0)) (s.mem.readW (off W (D + x + sz * k)) 32)) ?_ rfl)
    fun v ⟨⟨e1, e2, e3, z, mv⟩, kv⟩ => ?_
  · xrun [hb, aB, wB, hesi, aE, rE, src]
    have hc := (u.gpr .ecx).isLt
    have hW := W.isLt
    have l4 : (4 : BitVec 32).toNat = 4 := rfl
    have l1 : (1 : BitVec 32).toNat = 1 := rfl
    have l0 : (0 : BitVec 32).toNat = 0 := rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [BitVec.toNat_add, BitVec.toNat_ofNat, l4]; omega_using []
    · simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; rw [Nat.mul_succ]; omega_using []
    · simp only [BitVec.toNat_sub, l1]; omega_using [hk, hr, pcu]
    · rw [Bool.eq_iff_iff]
      simp only [beq_iff_eq, decide_eq_true_eq, BitVec.toNat_eq, BitVec.toNat_sub, l1, l0]
      omega_using [hk, hr, pcu]
  have Fv : Outside W S (4 * K) s.mem v.mem := fun y hy => by
    rw [mv, writeW32_outside _ _ _ (by omega_using [hK, hx, hD, hS, sep, pc, nw, hk, hr, pcu, mk, e1, e2, e3, hy]) y (by omega_using [hK, hx, hD, hS, sep, pc, nw, hk, hr, pcu, mk, e1, e2, e3, hy])]; exact Fu y hy
  have Vv : ∀ w < k + 1, VG.Proof.Mont.w32 v.mem W (S + 4 * w) = VG.Proof.Mont.w32 s.mem W (D + x + sz * w) :=
    fun w hw => by
      rw [mv]
      rcases Nat.lt_or_ge w k with hw' | hw'
      · rw [w32_write_ne (size := bytes) nw (by omega_using [hK, hx, hD, hS, sep, pc, nw, hk, hr, pcu, mk, e1, e2, e3, hw, hw']) (by omega_using [hK, hx, hD, hS, sep, pc, nw, hk, pcu, mk, e1, e2, e3, hw, hw']) (.inl (by omega_using [hw']))]; exact Vu w hw'
      · have : w = k := by omega_using [hw, hw']
        subst this
        rw [show S + 4 * w = S + 4 * w + 0 by omega_using [], w32_write_self]
  have Kv := Ku.trans kv
  by_cases last : k + 1 = K
  · left
    refine ⟨by change v.zf.map (!·) = some false; rw [z, show K - (k + 1) = 0 by omega_using [last]]; rfl, Fv,
      fun w hw => Vv w (by omega_using [last, hw]), Kv⟩
  · right
    refine ⟨by change v.zf.map (!·) = some true; rw [z, decide_eq_false (by omega_using [hK, hx, hD, hS, sep, pc, nw, hk, hr, pcu, mk, e1, e2, e3, last])]; rfl,
      rem - 1, by omega_using [hr], k + 1, by omega_using [hK, hD, hS, sep, pc, hk, hr, pcu, mk, e1, e2, e3, last], by omega_using [hK, hD, hS, sep, pc, hk, hr, pcu, mk, e1, e2, e3, last], wsu.of_keeps kv, e1, e2, by omega_using [e3], Kv, Fv, Vv⟩

theorem sv_val32 {m m' : Mem} {W : Addr} {b sz c : Nat} :
    ∀ {K}, (∀ w < K, VG.Proof.Mont.w32 m W (b + sz * w) = VG.Proof.Mont.w32 m' W (c + 4 * w)) →
      sv m W b sz K = val32 m' W c K
  | 0, _ => rfl
  | K + 1, h => by
    rw [sv, val32_succ, sv_val32 fun w hw => h w (by omega_using [hw]), h K (by omega_using [])]

/-! ## In the batch's working space -/

open VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.InvBatchRt (rv Bx kw_eq)

variable {L : Lay} {B : Addr} {Z len N n : Nat}

/-- The setup of `scatter` and `gather`: `esi` at element 0, `ebp` at `src`, `ecx = n + 1`. -/
theorem scatterSetup_ok {s : State} (h : Bx L s B Z len N n) {arr sz : Nat} {src : Ref}
    (ha : rv (kw len) { arr := arr, byte := sz } n < 2 ^ 32) (hs : rv (kw len) src n < 2 ^ 32)
    (hnb : 4 * n + 16 < 2 ^ 32) {Q : State → Prop}
    (k : ∀ u, Keeps [.ecx, .edx, .ebp, .esi] s u → u.mem = s.mem → PtrAt u B .esi (rv (kw len) { arr := arr } n + sz) →
      PtrAt u B .ebp (rv (kw len) src n) → (u.gpr .ecx).toNat = n + 1 → Q u) :
    WP isa (.block (ptr L .esi { arr := arr, byte := sz } .edx ++ ptr L .ebp src .edx ++ nBytes .ecx 1 ++
      [.shift .shr .ecx 2])) s Q := by
  have hZ := h.halfZ
  have hw := kw_bound h.ws.lenLe
  have ke := kw_eq len
  simp only [List.append_assoc]
  refine ptr_ok h.ws h.slots hZ (r := .esi) (t := .edx) (by decide) (by decide) (by decide) (by decide)
    (by intro e; cases e) ha fun u₁ K₁ m₁ p₁ => ?_
  have H₁ : Bx L u₁ B Z len N n := h.keep K₁ (by decide) (by decide) (o := 160) (c := 0)
    (by rw [m₁]; exact Outside.refl _ _ _ _) (Nat.le_refl _) (by have := h.fits16; omega_using [this])
  refine ptr_ok H₁.ws H₁.slots hZ (r := .ebp) (t := .edx) (by decide) (by decide) (by decide) (by decide)
    (by intro e; cases e) hs fun u₂ K₂ m₂ p₂ => ?_
  have m₁₂ : u₂.mem = s.mem := m₂.trans m₁
  have hs₂ : Scr u₂ B Z := H₁.ws.ws.workspace.of_keeps K₂ (by decide) (by decide)
  have sl₂ : Slots u₂.mem B (kw len) n := by rw [m₁₂]; exact h.slots
  refine nBytes_ok hs₂ sl₂ hZ hnb (by decide) fun u₃ K₃ m₃ c₃ => ?_
  refine WP.mono (WP.keeps [.ecx] (Q := fun v => (v.gpr .ecx).toNat = n + 1 ∧ v.mem = u₃.mem) ?_ rfl)
    fun v ⟨⟨cv, mv⟩, kv⟩ => k v (((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans
      ((K₃.mono (by decide)).trans (kv.mono (by decide)))) (by rw [mv, m₃, m₁₂]) ?_ ?_ cv
  · xrun []
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, c₃]
    omega_using []
  · rw [PtrAt, kv.1 _ (by decide), K₃.1 _ (by decide), K₂.1 _ (by decide)]
    rw [show rv (kw len) { arr := arr } n + sz = rv (kw len) { arr := arr, byte := sz } n by simp only [rv]; omega_using []]
    exact p₁
  · rw [PtrAt, kv.1 _ (by decide), K₃.1 _ (by decide)]; exact p₂

theorem scatter_ok {s : State} (h : Bx L s B Z len N n) {arr sz x : Nat} {src : Ref} (hx : x + 4 ≤ sz)
    (hfit : rv (kw len) { arr := arr } n + sz * (n + 2) < Z) (hA : sP + 8 ≤ rv (kw len) { arr := arr } n)
    (hsrc : rv (kw len) src n + 4 * (n + 1) ≤ Z)
    (sep : rv (kw len) src n + 4 * (n + 1) ≤ rv (kw len) { arr := arr } n + sz ∨
      rv (kw len) { arr := arr } n + sz + sz * (n + 1) ≤ rv (kw len) src n) :
    WP isa (scatter L arr sz x src) s fun t =>
      Bx L t B Z len N n ∧ RowWr B (rv (kw len) { arr := arr } n) sz x (n) s.mem t.mem ∧
      sv t.mem B (rv (kw len) { arr := arr } n + sz + x) sz (n + 1) = val32 s.mem B (rv (kw len) src n) (n + 1) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .esi] s t := by
  have hn := h.nowrap
  have m1 := mul_step (sz := sz) (show n + 1 < n + 2 by omega_using [])
  unfold scatter
  refine WP.seq (scatterSetup_ok h (arr := arr) (sz := sz) (src := src)
    (by rw [show rv (kw len) { arr := arr, byte := sz } n = rv (kw len) { arr := arr } n + sz by simp only [rv]; omega_using []]; omega_using [hfit, hn, m1])
    (by omega_using [hsrc, hn]) (by have := Nat.mul_le_mul_right (n + 2) (show 4 ≤ sz by omega_using [hx]); have := VG.Proof.Rsa.X86.InvBatchRt.rv_ge (kw len) { arr := arr } n; omega_arith)
    fun u K m pe pb pc => ?_)
  have scr := h.ws.ws.workspace
  have ws : Ws u B Z := ⟨K.2.2 ▸ scr.wr, scr.nowrap⟩
  refine WP.mono (scatterLoop_ok ws (by omega_using []) hx (by omega_using [hfit, m1]) hsrc (by omega_using [sep]) pb pe pc) fun t ⟨F, V, Kt⟩ => ?_
  rw [m] at F V
  have KK : Keeps [.eax, .ecx, .edx, .ebp, .esi] s t := (K.mono (by decide)).trans (Kt.mono (by decide))
  have R : RowWr B (rv (kw len) { arr := arr } n) sz x (n) s.mem t.mem := F.row
  refine ⟨h.keep KK (by decide) (by decide) (o := 160) (c := Z - 160) (fun y hy => R y (fun j hj => by
    have := mul_step (sz := sz) hj; unfold sP at hA; omega_using [hx, hfit, hA, hy, this]) (by unfold sP at *; omega_using [hfit, hA, hy])) (Nat.le_refl _) (by unfold sP at hA; omega_using [hfit, hA]), R, ?_, KK⟩
  exact sv_val32 fun w hw => V w hw

theorem gather_ok {s : State} (h : Bx L s B Z len N n) {arr sz x : Nat} {dst : Ref} (hx : x + 4 ≤ sz)
    (hfit : rv (kw len) { arr := arr } n + sz * (n + 2) < Z)
    (hdst : rv (kw len) dst n + 4 * (n + 1) ≤ Z)
    (sep : rv (kw len) dst n + 4 * (n + 1) ≤ rv (kw len) { arr := arr } n + sz ∨
      rv (kw len) { arr := arr } n + sz + sz * (n + 1) ≤ rv (kw len) dst n) :
    WP isa (gather L arr sz x dst) s fun t =>
      Bx L t B Z len N n ∧ Outside B (rv (kw len) dst n) (4 * (n + 1)) s.mem t.mem ∧
      val32 t.mem B (rv (kw len) dst n) (n + 1) = sv s.mem B (rv (kw len) { arr := arr } n + sz + x) sz (n + 1) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .esi] s t := by
  have hn := h.nowrap
  have m1 := mul_step (sz := sz) (show n + 1 < n + 2 by omega_using [])
  unfold gather
  refine WP.seq (scatterSetup_ok h (arr := arr) (sz := sz) (src := dst)
    (by rw [show rv (kw len) { arr := arr, byte := sz } n = rv (kw len) { arr := arr } n + sz by simp only [rv]; omega_using []]; omega_using [hfit, hn, m1])
    (by omega_using [hdst, hn]) (by have := Nat.mul_le_mul_right (n + 2) (show 4 ≤ sz by omega_using [hx]); have := VG.Proof.Rsa.X86.InvBatchRt.rv_ge (kw len) { arr := arr } n; omega_arith)
    fun u K m pe pb pc => ?_)
  have scr := h.ws.ws.workspace
  have ws : Ws u B Z := ⟨K.2.2 ▸ scr.wr, scr.nowrap⟩
  refine WP.mono (gatherLoop_ok ws (by omega_using []) hx (by omega_using [hfit, m1]) hdst (by omega_using [sep]) pb pe pc) fun t ⟨O, V, Kt⟩ => ?_
  rw [m] at O V
  have KK : Keeps [.eax, .ecx, .edx, .ebp, .esi] s t := (K.mono (by decide)).trans (Kt.mono (by decide))
  refine ⟨h.keep KK (by decide) (by decide) O (VG.Proof.Rsa.X86.InvBatchRt.rv_ge _ _ n) hdst, O, ?_, KK⟩
  exact (sv_val32 fun w hw => (V w hw).symm).symm

theorem val32_sv (m : Mem) (W : Addr) (b K : Nat) : val32 m W b K = sv m W b 4 K :=
  (sv_val32 fun _ _ => rfl).symm

/-! ## Header words of the start -/

open VG.Proof.Rsa.X86.InvBatchRt in
/-- `e`'s low word: 1. -/
theorem eOne_ok {s : State} (h : Bx L s B Z len N) :
    WP isa (.block (ptr L .eax { arr := deArr, byte := deSz } .edx ++
      [.mov .ecx (.imm 1), .store (at_ .eax 4) .ecx])) s fun t =>
      Bx L t B Z len N ∧ t.mem = s.mem.writeW (off B (de0 len + 4)) (1 : BitVec 32) ∧ Keeps [.eax, .ecx, .edx] s t := by
  have hn := h.nowrap
  have hZ := h.halfZ
  have hf16 := h.fits16
  have ke := kw_eq len
  have r11 : de0 len = 160 + 11 * (4 * kw len + 8) + 20 := by simp only [de0, rv_arr]; rfl
  refine ptr_ok h.ws h.slots hZ (r := .eax) (t := .edx) (by decide) (by decide) (by decide) (by decide)
    (by intro e; cases e) (by rw [← de0, r11]; omega_using [hn, hf16, ke]) fun u K m p => ?_
  rw [← de0] at p
  have scr := h.ws.ws.workspace
  have ws : Ws u B Z := ⟨K.2.2 ▸ scr.wr, scr.nowrap⟩
  have hp := ptr_eq p
  have aE := addr_off B (x := de0 len) (d := 4) (by omega_using [hn, hf16, ke, r11])
  have wE := ws_write ws (y := de0 len + 4) (n := 4) (by omega_using [hf16, ke, r11])
  refine WP.mono (WP.keeps [.ecx] (Q := fun v => v.mem = u.mem.writeW (off B (de0 len + 4)) (1 : BitVec 32)) ?_ rfl)
    fun v ⟨mv, kv⟩ => ?_
  · xrun [hp, aE, wE]
  · rw [m] at mv
    have KK : Keeps [.eax, .ecx, .edx] s v := (K.mono (by decide)).trans (kv.mono (by decide))
    have Om : Outside B (de0 len + 4) 4 s.mem v.mem := by rw [mv]; exact writeW32_outside _ _ _ (by omega_using [hn, hf16, ke, r11])
    exact ⟨h.keep KK (by decide) (by decide) Om (by omega_using [r11]) (by omega_using [hf16, ke, r11]), mv, KK⟩

open VG.Proof.Rsa.X86.InvBatchRt in
/-- The double batches' count, `(3 n + 2) / 2`. -/
theorem countF_ok {s : State} (h : Bx L s B Z len N) :
    WP isa (.block (nBytes .eax 0 ++ ([.shift .shr .eax 2, .mov .ecx (.reg .eax), .alu .add .eax (.reg .ecx),
      .alu .add .eax (.reg .ecx), .alu .add .eax (.imm 2), .shift .shr .eax 1, .store (sc 100) .eax] : List Instr))) s fun t =>
      Bx L t B Z len N ∧ t.mem = s.mem.writeW (off B 100) (BitVec.ofNat 32 ((3 * nw len + 2) / 2)) ∧
      Keeps [.eax, .ecx] s t := by
  have hn := h.nowrap
  have hZ := h.halfZ
  have hf16 := h.fits16
  have hw := kw_bound h.ws.lenLe
  have ke := kw_eq len
  refine nBytes_ok h.ws.ws.workspace h.slots hZ (by omega_using [hw]) (e := 0) (by decide) fun u K m c => ?_
  have scr := h.ws.ws.workspace
  have ws : Ws u B Z := ⟨K.2.2 ▸ scr.wr, scr.nowrap⟩
  have di : PtrAt u B .edi 0 := by
    rw [PtrAt, K.1 _ (by decide), RtWs.edi_eq h.ws, BitVec.toNat_ofNat]; omega_using []
  obtain ⟨hdi, aC, -⟩ := ptrRead ws di (d := 100) (by omega_using [hf16])
  simp only [Nat.zero_add] at aC
  have wC := ws_write ws (y := 100) (n := 4) (by omega_using [hf16])
  refine WP.mono (WP.keeps [.eax, .ecx] (Q := fun v =>
    v.mem = u.mem.writeW (off B 100) (BitVec.ofNat 32 ((3 * nw len + 2) / 2))) ?_ rfl) fun v ⟨mv, kv⟩ => ?_
  · xrun [sc, hdi, aC, wC]
    congr 1
    apply BitVec.eq_of_toNat_eq
    have l2 : (2 : BitVec 32).toNat = 2 := rfl
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_ofNat, c, l2]
    rw [ke]
    have : nw len ≤ 1026 := by omega
    generalize nw len = q at *
    simp only [Nat.reducePow, Nat.mul_zero, Nat.add_zero]
    have e1 : 4 * (2 * q / 2) / 4 = q := by omega_using []
    rw [e1, Nat.mod_eq_of_lt (a := q + q) (by omega_using [this]), Nat.mod_eq_of_lt (a := q + q + q) (by omega_using [this]),
      Nat.mod_eq_of_lt (a := q + q + q + 2) (by omega_using [this]), Nat.mod_eq_of_lt (a := (3 * q + 2) / 2) (by omega_using [this])]
    omega_using []
  · rw [m] at mv
    have KK : Keeps [.eax, .ecx] s v := (K.mono (by decide)).trans kv
    have Om : Outside B 100 4 s.mem v.mem := by rw [mv]; exact writeW32_outside _ _ _ (by omega_using [])
    exact ⟨h.keepHigh KK (by decide) (by decide) Om (by decide) (by omega_using [hf16]), mv, KK⟩

end VG.Proof.Rsa.X86.InvBatchRt.F

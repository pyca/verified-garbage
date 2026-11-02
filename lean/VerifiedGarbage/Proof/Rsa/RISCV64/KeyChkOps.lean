module

public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyChkBase
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyOps
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-! # The checks of an RSA key on RISC-V: the steps

As on PPC64LE (`Proof/Rsa/PPC64LE/KcOps.lean`), each from `Stg`: copies,
clearing a low bit, comparisons and'ed into the mask (`ltA_ok`, `eqA_ok`),
and the counts of the products modulo a number (`cnt33_ok`, `cntQ_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.KeyCheck

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (seqs copy clrLow andS stBorrow sOdd sB sC)
open VG.Impl.Rsa.RISCV64.KeyCheck
open VG.Proof.Rsa.KeyWorkspace (upd upd_ne upd_self)

theorem kc_seqs_cons {c : Prog isa} {l : List (Prog isa)} (hl : l ≠ []) {s : State} {Q : State → Prop} :
    WP isa (seqs (c :: l)) s Q ↔ WP isa c s (fun t => WP isa (seqs l) t Q) := by
  match l, hl with
  | _ :: _, _ => exact WP.seq_iff

theorem kc_seqs_append {l₁ l₂ : List (Prog isa)} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) {s : State}
    {Q : State → Prop} :
    WP isa (seqs (l₁ ++ l₂)) s Q ↔ WP isa (seqs l₁) s (fun t => WP isa (seqs l₂) t Q) := by
  induction l₁ generalizing s with
  | nil => exact absurd rfl h₁
  | cons c l ih =>
    rcases l with _ | ⟨d, l⟩
    · exact kc_seqs_cons h₂
    · rw [List.cons_append, kc_seqs_cons (by simp), kc_seqs_cons (by simp)]
      exact ⟨fun h => WP.mono h fun t ht => (ih (by simp)).mp ht,
        fun h => WP.mono h fun t ht => (ih (by simp)).mpr ht⟩

theorem opRegs_body : ∀ x ∈ opRegs, x ∈ bodyRegs := by decide

/-- `copy o a`, `o` then tracked. -/
theorem Stg.copy_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {o a : Nat} (ho : o < nArr) (ha : a ∈ live) (hoa : o ≠ a) :
    WP isa (copy o a) s (Stg g s0 (upd A o (A a)) (o :: live) c) := by
  refine WP.mono (Keys.copy_ok h.ws ho (h.live_lt a ha) (by decide) hoa) fun t ⟨ht, k, e, r, out⟩ => ?_
  refine h.next ht k (by simpa using ho) (by simp) r opRegs_body ?_ ?_ ?_ (h.mask_keep k (by simp))
  · have e' : num t.mem g.B g.w o = A a := e.trans (h.arrs.get ha)
    exact (h.arrs_write k e' (fun j _ => (Decidable.em (j = o)).imp_right fun n => by simpa using n)
      (by simp)).cons (by rw [upd_self]; exact e')
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj'
    · exact ho
    · exact h.live_lt j hj'
  · by_cases hv : o = aVD
    · subst hv
      have hS : S g.w = 8 * (g.w + 2) := rfl
      rw [out.word (by omega) (by have := h.ws.fit64 (j := aVD) (by decide); omega), h.vdTop]
    · exact h.vd_keep k (by simpa using hv) (by simp)

/-- `clrLow j`, for `j` not the divisor. -/
theorem Stg.clrLow_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {j : Nat} (hj : j ∈ live) (hjv : j ≠ aVD) :
    WP isa (.block (clrLow j)) s (Stg g s0 (upd A j (A j / 2 * 2)) live c) := by
  refine WP.mono (Keys.clrLow_ok h.ws (h.live_lt j hj) (by decide)) fun t ⟨ht, k, e, r⟩ => ?_
  exact h.next ht k (by simpa using h.live_lt j hj) (by simp) r opRegs_body
    (h.arrs_write k (by rw [e, h.arrs.get hj]) (fun i _ => (Decidable.em (i = j)).imp_right fun n => by
      simpa using n) (by simp)) h.live_lt (h.vd_keep k (by simpa using hjv) (by simp))
    (h.mask_keep k (by simp))

/-- The check in `sF` and'ed into the mask. -/
theorem Stg.acc_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c d : Bool}
    (h : Stg g s0 A live c s) (hf : slot s.mem g.B sF = if d then 1 else 0) :
    WP isa (.block acc) s (Stg g s0 A live (c && d)) := by
  refine WP.mono (andS_ok h.ws (d := sMask) (a := sMask) (b := sF) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (bit_le h.mask) (bit_le hf)) fun t ⟨ht, k, e, r⟩ => ?_
  refine h.next ht k (by simp) (by decide) r opRegs_body (h.arrs_keep k (by simp) (by decide)) h.live_lt
    (h.vd_keep k (by simp) (by decide)) ?_
  rw [e, acc_bits h.mask hf]

/-- `ltA a b`: the mask and'ed with `[a] < [b]`. -/
theorem Stg.ltA_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {a b : Nat} (ha : a ∈ live) (hb : b ∈ live) (hW : aW ∉ live) :
    WP isa (seqs (ltA a b)) s (Stg g s0 A live (c && decide (A a < A b))) := by
  have na := h.live_lt a ha
  have nb := h.live_lt b hb
  have hWa : aW ≠ a := fun e => hW (e ▸ ha)
  have hWb : aW ≠ b := fun e => hW (e ▸ hb)
  rw [ltA, kc_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h.ws (o := aW) (a := a) (b := b) (by decide) na nb (by decide) hWa hWb)
    fun t1 ⟨h1, k1, v1, b1, r1⟩ => ?_
  have g1 : Stg g s0 A live c t1 :=
    h.next h1 k1 (by decide) (by simp) r1 opRegs_body
      (h.arrs_keep k1 (fun j hj e => hW (by simp at e; exact e ▸ hj)) (by simp)) h.live_lt
      (h.vd_keep k1 (by decide) (by simp)) (h.mask_keep k1 (by simp))
  rw [show seqs [.block (stBorrow sF ++ acc)] = .block (stBorrow sF ++ acc) from rfl, WP.block_append_iff]
  refine WP.mono (stBorrow_ok h1 (sl := sF) (by decide) (by decide)) fun t2 ⟨h2, k2, s2, r2⟩ => ?_
  have g2 : Stg g s0 A live c t2 :=
    g1.next h2 k2 (by simp) (by decide) r2 (by simp) (g1.arrs_keep k2 (by simp) (by decide))
      g1.live_lt (g1.vd_keep k2 (by simp) (by decide)) (g1.mask_keep k2 (by decide))
  refine g2.acc_ok ?_
  rw [s2]
  have lo : num t1.mem g.B g.w aW < 2 ^ (64 * g.w) := wordsVal_lt _ _ _ _
  have la : num s.mem g.B g.w a < 2 ^ (64 * g.w) := wordsVal_lt _ _ _ _
  have lb : num s.mem g.B g.w b < 2 ^ (64 * g.w) := wordsVal_lt _ _ _ _
  rw [h.arrs.get ha, h.arrs.get hb] at v1
  rw [h.arrs.get ha] at la
  rw [h.arrs.get hb] at lb
  by_cases hlt : A a < A b
  · have : (t1.gpr .t4).toNat = 1 := by
      rcases Nat.lt_or_ge (t1.gpr .t4).toNat 1 with e | e
      · have : (t1.gpr .t4).toNat = 0 := by omega
        rw [this, Nat.mul_zero, Nat.add_zero] at v1; omega
      · omega
    simp [hlt, this]
  · have : (t1.gpr .t4).toNat = 0 := by
      rcases Nat.lt_or_ge (t1.gpr .t4).toNat 1 with e | e
      · omega
      · have : (t1.gpr .t4).toNat = 1 := by omega
        rw [this, Nat.mul_one] at v1; omega
    simp [hlt, this]

/-- `eqA a b`: the mask and'ed with `[a] = [b]`. -/
theorem Stg.eqA_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {a b : Nat} (ha : a ∈ live) (hb : b ∈ live) :
    WP isa (seqs (eqA a b)) s (Stg g s0 A live (c && decide (A a = A b))) := by
  have na := h.live_lt a ha
  have nb := h.live_lt b hb
  rw [eqA, kc_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok h.ws (d := sF) (a := a) (b := b) na nb (by decide) (by decide) (by decide))
    fun t1 ⟨h1, k1, e1, r1⟩ => ?_
  have g1 : Stg g s0 A live c t1 :=
    h.next h1 k1 (by simp) (by decide) r1 opRegs_body (h.arrs_keep k1 (by simp) (by decide)) h.live_lt
      (h.vd_keep k1 (by simp) (by decide)) (h.mask_keep k1 (by decide))
  rw [show seqs [.block acc] = .block acc from rfl]
  refine g1.acc_ok ?_
  rw [e1, h.arrs.get ha, h.arrs.get hb]
  by_cases he : A a = A b <;> simp [he]

/-- `33` into `s7`. -/
theorem cnt33_ok (u : State) :
    WP isa (.block cnt33) u fun u' => (u'.gpr .s7 = BitVec.ofNat 64 33 ∧ u'.mem = u.mem) ∧ Keep [.s7] u u' := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  have e : exec (.li .s7 33) u = some (u.write .s7 (BitVec.ofNat 64 33)) := by
    rw [exec_li (by decide)]; rfl
  brun [cnt33, e]

/-- `8 a` steps, from `q_len = a` in `s6`. -/
theorem cntQ_ok {u : State} {a : Nat} (h : u.gpr .s6 = BitVec.ofNat 64 a) :
    WP isa (.block cntQ) u fun u' =>
      (u'.gpr .s7 = BitVec.ofNat 64 (8 * a) ∧ u'.mem = u.mem) ∧ Keep [.s7] u u' := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  have e : BitVec.ofNat 64 a <<< 3 = BitVec.ofNat 64 (8 * a) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega_arith
  brun [cntQ, h, e]

end VG.Proof.Rsa.RISCV64.KeyCheck

module

public import VerifiedGarbage.Proof.Rsa.Arm.KcEntry
import VerifiedGarbage.Proof.Rsa.Arm.CvLoad
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
import VerifiedGarbage.Proof.Rsa.Arm.InvParts
import VerifiedGarbage.Proof.Bignum.Arm.LoadBE
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rsa.Arm.CvLoads

/-! # The checks of an RSA key on ARMv7: the numbers read into arrays

`EntSt.load_ok`: `load j` reads a number into array `j`; `loads_ok`: the
numbers on the stack, by induction over the list of them.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.Rsa.Arm.Keys VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm
open VG.Proof.Rsa.Arm.CrtValues (reg val32_off Keep.of_frame_arr bytes_frame)

section
variable {nA iS : Nat} {ins : List (Nat × Nat)}

/-- The number at `src`, `k` bytes long. -/
abbrev bytesV (σ : State) (src : BitVec 32) (k : Nat) : Nat :=
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt σ.mem (State.addr src) k)

theorem EntSt.of_rest {σ s t : State} {A : Nat → Nat} (h : EntSt nA iS ins σ s A) {ws : List Reg}
    (r : Rest ws s t) (m : t.mem = s.mem) (h10 : Reg.r10 ∉ ws) (h11 : Reg.r11 ∉ ws) (h7 : Reg.r7 ∉ ws)
    (h8 : Reg.r8 ∉ ws) (h9 : Reg.r9 ∉ ws) : EntSt nA iS ins σ t A :=
  ⟨h.base.of_rest r m, h.ws.rest r h7 h8 h9, m ▸ h.cnt, fun j hj => m ▸ h.full j hj,
    (r.gpr _ h10).trans h.r10, (r.gpr _ h11).trans h.r11⟩

/-- `load j`: array `j` := the `k` bytes at `r4` (`r6 = k`). -/
theorem EntSt.load_ok {σ s : State} {A : Nat → Nat} (h : EntSt nA iS ins σ s A) {j : Nat} (hj : j < nArr)
    {src : BitVec 32} {k : Nat} (hrd : reg src k ∈ σ.rd) (hsep : (reg src k).Disjoint (rS iS σ))
    (fit : src.toNat + k ≤ 2 ^ 32) (pos : 0 < k) (le : k ≤ fK σ)
    (p4 : s.gpr .r4 = src) (p6 : s.gpr .r6 = BitVec.ofNat 32 k) :
    WP isa (CrtValues.load j) s fun t => EntSt nA iS ins σ t (upd A j (bytesV σ src k)) ∧
      Rest [.r0, .r1, .r2, .r3, .r5, .lr] s t := by
  have pre := h.base.pre
  have hw := h.ws
  have fit' := hw.arr_fit hj
  have nw := hw.nowrap
  have w16 := pre.w16
  have kb := pre.kb
  have hS : S (geo iS σ).w = 4 * ((geo iS σ).w + 2) := rfl
  have hkw : k ≤ 4 * (geo iS σ).w := by
    have : (geo iS σ).w = (fK σ + 3) / 4 := rfl
    omega_arith
  have hB : (geo iS σ).B.toNat + (arr (geo iS σ).w j + 4 * ((geo iS σ).w + 2)) ≤ 2 ^ 32 := by
    have f2 : arr (geo iS σ).w j + 4 * ((geo iS σ).w + 2) ≤ (geo iS σ).Z := hw.arr_fit hj
    have := hw.nowrap
    omega_arith
  rw [CrtValues.load, WP.seq_iff]
  refine ptr_ok hw (by decide) (by simp only [nArr] at hj; omega_arith) fun s1 p1 r1 m1 h1 => ?_
  refine wp_mov (op2_reg _ _) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun u u4 => WP.block_nil ?_
  have rest : Rest [.r0, .r3, .r5, .lr] s u :=
    (r1.mono (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans (u4.rest (by simp))))
  have mu : u.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, m1]
  have bu := h.base.of_rest rest mu
  have hu := hw.rest rest
  have ad : State.addr ((geo iS σ).B + BitVec.ofNat 32 (arr (geo iS σ).w j)) =
      off (State.addr (geo iS σ).B) (arr (geo iS σ).w j) := hw.addr (by omega_arith)
  have p0 : u.gpr .r0 = (geo iS σ).B + BitVec.ofNat 32 (arr (geo iS σ).w j) := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), p1]
  refine WP.mono (loadBE_ok u (src := src) (dst := (geo iS σ).B + BitVec.ofNat 32 (arr (geo iS σ).w j))
    (n := (geo iS σ).w + 2) pos (by omega_arith) (by omega_arith) fit
    (by rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith),
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith)
    ⟨reg src k, List.mem_append_left _ (by rw [bu.rd]; exact hrd), Region.contains_self _ _⟩
    ⟨rS iS σ, by rw [bu.wr, pre.wr]; simp, by rw [ad]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    (by rw [ad]
        refine fun a ha hb => hsep a ha ?_
        exact Region.Contains.byte (r := rS iS σ) (b := off (State.addr (geo iS σ).B) (arr (geo iS σ).w j))
          (n := 4 * ((geo iS σ).w + 2)) (Offset.contains_base _ (by omega_arith) (by omega_arith))
          (by simp only [Region.Contains] at hb ⊢; omega_arith))
    p0 (by rw [rest.gpr _ (by decide), p4])
    (by rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, p1])
    (by rw [rest.gpr _ (by decide), p6])
    (by rw [u4.other _ (by decide), u3.gpr, dpVal, u2.other .r9 (by decide), r1.gpr .r9 (by decide), hw.r9,
          BitVec.ofNat_add]; rfl)
    (by rw [u4.gpr])) ?_
  rintro t ⟨v, f, r⟩
  rw [ad] at f v
  have k' : Keep (geo iS σ).B (geo iS σ).w [j] [] u.mem t.mem := Keep.of_frame_arr f (by omega_arith)
  have RT : Rest [.r0, .r1, .r2, .r3, .r5, .lr] s t := (rest.mono (by simp)).trans (r.mono (by simp))
  refine ⟨⟨bu.keep k' (by simpa using hj) (by simp) (by simp) r.sp r.rd r.wr, hu.rest r, ?_, fun i hi => ?_,
    (RT.gpr _ (by decide)).trans h.r10, (RT.gpr _ (by decide)).trans h.r11⟩, RT⟩
  · rw [slot_eq_of_keep k' (by decide) (by simp), mu, h.cnt]
  · simp only [upd]
    split
    · subst i
      rw [val32_off, Nat.add_zero] at v
      rw [v, mu, bytes_frame h.base.frame (by simpa using hsep) (by omega_arith)]
    · rename_i hne
      rw [k'.full (by simpa using fun e => hne e.symm) (by simp) (hw.fit64 hi), mu, h.full i hi]

/-- The `i`-th input on the stack. -/
abbrev inV (σ : State) (i : Nat) : Nat := bytesV σ (stackArg σ i) (stackArg σ (i + 1)).toNat

/-- `loadArg (4 i) j`: array `j` := the input at stack word `i`. -/
theorem EntSt.loadArg_ok {σ s : State} {A : Nat → Nat} (h : EntSt nA iS ins σ s A) {p : Nat × Nat}
    (hp : p ∈ ins) {rest : List (Prog isa)} (hr : rest ≠ []) {Q : State → Prop}
    (k : ∀ t, EntSt nA iS ins σ t (upd A p.2 (inV σ p.1)) → WP isa (seqs rest) t Q) :
    WP isa (seqs (loadArg (4 * p.1) p.2 ++ rest)) s Q := by
  have pre := h.base.pre
  have hA := pre.hA
  have hi := pre.hIns p hp
  have hn := pre.ins1 p hp
  unfold loadArg CrtValues.args
  rw [List.cons_append, List.cons_append, List.nil_append, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine h.base.ldrSp (i := p.1) (by omega_arith) (by omega_arith) fun s1 b1 u1 => ?_
  have e : 4 * p.1 + 4 = 4 * (p.1 + 1) := by omega_arith
  rw [e]
  refine b1.ldrSp (i := p.1 + 1) hi.1 (by omega_arith) fun s2 b2 u2 => WP.block_nil ?_
  have h2 : EntSt nA iS ins σ s2 A :=
    (h.of_rest ((u1.rest (ws := [.r4, .r6]) (by simp)).trans (u2.rest (ws := [.r4, .r6]) (by simp)))
      (u2.mem.trans u1.mem) (by decide) (by decide) (by decide) (by decide) (by decide))
  rw [wp_seqs_cons hr]
  refine WP.mono (h2.load_ok hi.2.1 (src := stackArg σ p.1) (k := (stackArg σ (p.1 + 1)).toNat)
    (pre.rdIns p hp) (pre.insS p hp) (pre.fIns p hp) hn.1 hn.2
    (by rw [u2.other _ (by decide), u1.gpr]) (by rw [u2.gpr]; simp)) fun t ⟨ht, _⟩ => k t ht

/-- What the loads of `l` leave, from `A`. -/
def loadFn (σ : State) : List (Nat × Nat) → (Nat → Nat) → Nat → Nat
  | [], A => A
  | p :: l, A => loadFn σ l (upd A p.2 (inV σ p.1))

theorem EntSt.loads_ok {σ s : State} {A : Nat → Nat} (h : EntSt nA iS ins σ s A) (l : List (Nat × Nat))
    (hl : ∀ p ∈ l, p ∈ ins) {rest : List (Prog isa)} (hr : rest ≠ []) {Q : State → Prop}
    (k : ∀ t, EntSt nA iS ins σ t (loadFn σ l A) → WP isa (seqs rest) t Q) :
    WP isa (seqs ((l.map fun p => (4 * p.1, p.2)).flatMap (fun a => loadArg a.1 a.2) ++ rest)) s Q := by
  induction l generalizing s A with
  | nil => exact k s h
  | cons p l ih =>
    rw [List.map_cons, List.flatMap_cons, List.append_assoc]
    exact h.loadArg_ok (hl p List.mem_cons_self) (by simp [hr]) fun t ht =>
      ih ht (fun q hq => hl q (List.mem_cons_of_mem _ hq)) k

end

end VG.Proof.Rsa.Arm.KeyCheck

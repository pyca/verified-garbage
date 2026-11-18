module

public meta import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Rsa.X86.KeyScalar
public import VerifiedGarbage.Impl.Rsa.X86.Inverse
public import VerifiedGarbage.Proof.Rsa.InverseArithmetic
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Rsa.X86.KeySub
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Rsa.X86.KeySelect`, which this module and modules that import it used -/

section

/-! # Constant-address array selection in the RSA key workspace -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Keys
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot

theorem sel_ok {s : State} {B : Addr} {Z w N o a b sl : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hs : sl + 4 ≤ hdr)
    (bit : slot s.mem B sl ≤ 1) :
    WP isa (sel w o a b sl) s fun t =>
      Ws t B Z w N ∧ Keep B w [o] [] s.mem t.mem ∧
      num t.mem B w o = (if slot s.mem B sl = 0 then num s.mem B w a else num s.mem B w b) ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have fo := h.arr_fit ho
  have fa := h.arr_fit ha
  have fb := h.arr_fit hb
  have head := h.hdr_le
  have sep (j : Nat) : o = j ∨ arr w o + 4 * w ≤ arr w j ∨ arr w j + 4 * w ≤ arr w o := by
    by_cases eq : o = j
    · exact .inl eq
    · have := arr_disj (w := w) eq; unfold S at this; exact .inr (by omega_using [this])
  unfold sel
  change WP isa (.seq _ (VG.Impl.Mont.X86.Dynamic.selectsW w (arr w a) (arr w b) (arr w o))) s _
  refine WP.seq (wp_movS rfl fun u U _ => ?_)
  have hu := h.workspace.of_keeps U.keeps (by decide)
  refine wp_subS (readSrc_sc hu (by omega_using [hs, head])) fun v V _ => WP.block_nil ?_
  have mem : v.mem = s.mem := V.mem.trans U.mem
  have mask : v.gpr .ecx = if decide (slot s.mem B sl ≠ 0) then BitVec.allOnes 32 else 0 := by
    rw [V.gpr, U.gpr, U.mem]
    have word : s.mem.readW (off B sl) 32 = BitVec.ofNat 32 (slot s.mem B sl) := by
      simp [slot, w32]
    rw [word]
    have cases : slot s.mem B sl = 0 ∨ slot s.mem B sl = 1 := by omega_using [bit]
    rcases cases with e | e <;> rw [e] <;> rfl
  have hv := hu.of_keeps V.keeps (by decide)
  simp only [S] at fo fa fb
  refine WP.mono (selectsW_ok hv _ mask h.wpos (by omega_using [fa]) (by omega_using [fb]) (by omega_using [fo]) ?_ ?_) ?_
  · rcases sep a with e | e; exact .inl (congrArg (arr w) e); exact .inr e
  · rcases sep b with e | e; exact .inl (congrArg (arr w) e); exact .inr e
  rintro t ⟨frame, value, rest⟩
  have r : Keeps [.eax, .ecx, .edx, .ebp] s t :=
    ((U.keeps.trans V.keeps).mono (by decide)).trans (rest.mono (by decide))
  refine ⟨h.rest r, ?_, ?_, r⟩
  · rw [mem] at frame
    exact Keep.of_arr (d := 0) (by simpa using frame) (by unfold S; omega_using []) (by simp)
  · change val32 t.mem B (arr w o) w = _
    rw [value, mem]
    by_cases e : slot s.mem B sl = 0 <;> simp [e, num]
end VG.Proof.Rsa.X86.Keys

end

end

/-! # Subtraction modulo the odd RSA inverse modulus -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Keys
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Proof.Rsa (subMod halfMod)

theorem wp_seqs_cons {c : Prog isa} {l : List (Prog isa)} (hl : l ≠ []) {s : State} {Q : State → Prop} :
    WP isa (seqs (c :: l)) s Q ↔ WP isa c s (fun t => WP isa (seqs l) t Q) := by
  match l, hl with
  | _ :: _, _ => exact WP.seq_iff

theorem wp_seqs_append {l₁ l₂ : List (Prog isa)} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) {s : State}
    {Q : State → Prop} :
    WP isa (seqs (l₁ ++ l₂)) s Q ↔ WP isa (seqs l₁) s (fun t => WP isa (seqs l₂) t Q) := by
  induction l₁ generalizing s with
  | nil => exact absurd rfl h₁
  | cons c l ih =>
    rcases l with _ | ⟨d, l⟩
    · exact wp_seqs_cons h₂
    · rw [List.cons_append, wp_seqs_cons (by simp), wp_seqs_cons (by simp)]
      exact ⟨fun h => WP.mono h fun t ht => (ih (by simp)).mp ht,
        fun h => WP.mono h fun t ht => (ih (by simp)).mpr ht⟩

/-- Index side conditions. -/
macro "idx" : tactic => `(tactic| plain_simp_names ((try simp only [aM, aNM, aZero, aT1, aT2, aT3, aT4, sOdd, sB, sC, sT,
  List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and, hdr, ne_eq]) <;> omega_arith))

end VG.Proof.Rsa.X86.Keys

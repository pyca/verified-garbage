module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Division
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics

/-! # Divide persistent arrays in the full native RSA workspace -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr
open VG.Proof.RsaKeyGen.X86.Key (DivisionInputs DivisionOutputs)

def arrayDivisionRanges (n q r : Nat) : List (Nat × Nat) :=
  [(VG.Impl.Rsa.X86.Keys.hdr, 4 * S n), (136, 4), (140, 4),
    (arr n q, 4 * n), (arr n r, 4 * n)]

theorem arrayDivision_ok {s : State} {B : Addr} {Z n a d q r : Nat} (h : Ws s B Z n 32)
    (ha : a < 32) (hd : d < 32) (hq : q < 32) (hr : r < 32)
    (pa : 4 ≤ a) (pd : 4 ≤ d) (pq : 4 ≤ q) (pr : 4 ≤ r) (qr : q ≠ r)
    (positive : 0 < num s.mem B n d) :
    WP isa (divFull a d q r) s fun t =>
      Ws t B Z n 32 ∧ Outs B (arrayDivisionRanges n q r) s.mem t.mem ∧
      num t.mem B n q = num s.mem B n a / num s.mem B n d ∧
      num t.mem B n r = num s.mem B n a % num s.mem B n d ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have fa := h.arr_fit ha
  have fd := h.arr_fit hd
  have fq := h.arr_fit hq
  have fr := h.arr_fit hr
  have input : DivisionInputs Z n (arr n a) (arr n d) := by
    refine ⟨?_, ?_, Or.inr (arr_mono pa), Or.inr (arr_mono pd)⟩
    · unfold S at fa
      omega
    · unfold S at fd
      omega
  have output : DivisionOutputs Z n (arr n q) (arr n r) := by
    refine ⟨?_, ?_, Or.inr (arr_mono pq), Or.inr (arr_mono pr), ?_⟩
    · unfold S at fq
      omega
    · unfold S at fr
      omega
    · have disj := arr_disj (w := n) qr
      unfold S at disj
      omega
  refine WP.mono (divisionFrom_ok h (by decide) (by decide)
    (show DivisionInputs Z (Width.modulus.words n)
      ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr a).offset n)
      ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr d).offset n) from input)
    (show DivisionOutputs Z (Width.modulus.words n)
      ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr q).offset n)
      ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr r).offset n) from output) positive)
    fun t ⟨ht, O, Q, R, K⟩ => ?_
  exact ⟨ht, by simpa only [arrayDivisionRanges, divisionRanges, Width.words,
    VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array, S,
    VG.Impl.Rsa.X86.KeyRt.sCy, VG.Impl.Rsa.X86.KeyRt.sQb, Nat.mul_assoc] using O,
    Q, R, K.mono (by decide)⟩

theorem arrayDivision_preserves_num {m m' : Mem} {B : Addr} {n q r j : Nat}
    (persistent : 4 ≤ j) (jq : j ≠ q) (jr : j ≠ r) (fit : arr n j + S n ≤ 2 ^ 64)
    (O : Outs B (arrayDivisionRanges n q r) m m') : num m' B n j = num m B n j := by
  change val32 m' B (arr n j) n = val32 m B (arr n j) n
  apply O.val32 _ (by unfold S at fit; omega)
  intro region mem
  simp only [arrayDivisionRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (arr_mono persistent)
  · exact Or.inr (Nat.le_trans (by decide : 136 + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) (Nat.le_add_right ..))
  · exact Or.inr (Nat.le_trans (by decide : 140 + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) (Nat.le_add_right ..))
  · have D := arr_disj (w := n) jq
    simp only at D ⊢
    unfold S at D
    omega
  · have D := arr_disj (w := n) jr
    simp only at D ⊢
    unfold S at D
    omega

end VG.Proof.RsaKeyGen.X86.KeyRuntime

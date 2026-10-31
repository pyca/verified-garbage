module

public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.Copy
public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.Prepare
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Lay

/-! # Bounds and separation of prepared-key buffers -/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.PreparedKey

abbrev input (bytes : Nat) : List (Reg × Nat) := [(.x25, bytes)]
abbrev output (bytes count : Nat) : List (Reg × Nat) :=
  [(.x26, bytes + 1024 * count), (.x28, 1024)]

theorem in25 (bytes count o len : Nat) :
    inB (input bytes ++ output bytes count) (.x25, o) len = decide (o + len ≤ bytes) := rfl

theorem in26 (bytes count o len : Nat) :
    inB (input bytes ++ output bytes count) (.x26, o) len = decide (o + len ≤ bytes + 1024 * count) := rfl

theorem in28 (bytes count o len : Nat) :
    inB (input bytes ++ output bytes count) (.x28, o) len = decide (o + len ≤ 1024) := rfl

theorem out26 (bytes count o len : Nat) :
    inB (output bytes count) (.x26, o) len = decide (o + len ≤ bytes + 1024 * count) := rfl

theorem out28 (bytes count o len : Nat) :
    inB (output bytes count) (.x28, o) len = decide (o + len ≤ 1024) := rfl

theorem sep25_26 (bytes count o len o' len' : Nat) :
    sepB (input bytes) (output bytes count) (.x25, o) len (.x26, o') len' =
      (decide (o + len ≤ bytes) && decide (o' + len' ≤ bytes + 1024 * count)) := by
  rw [sepB_ne (by decide) rfl, in25, in26]

theorem sep26_28 (bytes count o len o' len' : Nat) :
    sepB (input bytes) (output bytes count) (.x26, o) len (.x28, o') len' =
      (decide (o + len ≤ bytes + 1024 * count) && decide (o' + len' ≤ 1024)) := by
  rw [sepB_ne (by decide) rfl, in26, in28]

theorem sep25_28 (bytes count o len o' len' : Nat) :
    sepB (input bytes) (output bytes count) (.x25, o) len (.x28, o') len' =
      (decide (o + len ≤ bytes) && decide (o' + len' ≤ 1024)) := by
  rw [sepB_ne (by decide) rfl, in25, in28]

theorem public_checks {p : Params}
    (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {i : Nat} (hi : i < p.k) :
    rwChk (input p.pkLen) (output p.pkLen p.k)
      (.x25, 32 + 320 * i) 320 (.x26, p.pkLen + 1024 * i) 1024 = true ∧
    ipChk (input p.pkLen) (output p.pkLen p.k)
      (.x26, p.pkLen + 1024 * i) (.x28, 0) = true := by
  have hk := (KeyGen.pfacts hp).k
  have hpk := (KeyGen.pfacts hp).pk
  constructor <;> simp only [rwChk, ipChk, sep25_26, sep26_28, in25, in26, in28, out26, out28,
    Bool.and_eq_true, decide_eq_true_eq] <;> omega

theorem public_copy_check {p : Params}
    (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    copyChk (input p.pkLen) (output p.pkLen p.k)
      (.x26, 0) (.x25, 0) p.pkLen = true := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem secret_copy_check {p : Params}
    (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    copyChk (input p.skLen) (output p.skLen (p.ℓ + 2 * p.k))
      (.x26, 0) (.x25, 0) p.skLen = true := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem secret_checks {p : Params}
    (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {i : Nat}
    (hi : i < p.ℓ + 2 * p.k) :
    let (src, len, a, b) := secretPiece p i
    rwChk (input p.skLen) (output p.skLen (p.ℓ + 2 * p.k))
      (.x25, src) len (.x26, p.skLen + 1024 * i) 1024 = true ∧
    ipChk (input p.skLen) (output p.skLen (p.ℓ + 2 * p.k))
      (.x26, p.skLen + 1024 * i) (.x28, 0) = true ∧ BpOk a b len := by
  have hs44 : secretLen mlDsa44 = 96 := by decide
  have hs65 : secretLen mlDsa65 = 128 := by decide
  have hs87 : secretLen mlDsa87 = 96 := by decide
  have hk44 : mlDsa44.skLen = 2560 := by decide
  have hk65 : mlDsa65.skLen = 4032 := by decide
  have hk87 : mlDsa87.skLen = 4896 := by decide
  rcases hp with rfl | rfl | rfl <;>
    dsimp only [secretPiece] <;> split <;>
    simp only [hs44, hs65, hs87, hk44, hk65, hk87, mlDsa44, mlDsa65, mlDsa87,
      rwChk, ipChk, sep25_26, sep26_28, in25, in26, in28, out26, out28,
      Bool.and_eq_true, decide_eq_true_eq] at * <;>
    refine ⟨by omega, by omega, ?_⟩ <;>
    exact ⟨by decide, by decide, by decide⟩

theorem public_keep_source {p : Params}
    (_hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {i : Nat} (hi : i < p.k) :
    keepB (input p.pkLen) (output p.pkLen p.k)
      [((.x26, p.pkLen + 1024 * i), 1024), ((.x28, 0), 1024)]
      (.x25, 0) p.pkLen = true := by
  simp only [keepB, List.all_cons, List.all_nil, Bool.and_true,
    sep25_26, sep25_28, in25, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem public_keep_prefix {p : Params}
    (_hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {i : Nat} (hi : i < p.k) :
    keepB (input p.pkLen) (output p.pkLen p.k)
      [((.x26, p.pkLen + 1024 * i), 1024), ((.x28, 0), 1024)]
      (.x26, 0) p.pkLen = true := by
  simp only [keepB, List.all_cons, List.all_nil, Bool.and_true, sepB_same,
    sep26_28, in26, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  omega

theorem public_keep_prior {p : Params}
    (_hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {i j : Nat}
    (hi : i < p.k) (hj : j < i) :
    keepB (input p.pkLen) (output p.pkLen p.k)
      [((.x26, p.pkLen + 1024 * i), 1024), ((.x28, 0), 1024)]
      (.x26, p.pkLen + 1024 * j) 1024 = true := by
  simp only [keepB, List.all_cons, List.all_nil, Bool.and_true, sepB_same,
    sep26_28, in26, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  omega

theorem row_keep_source (bytes count : Nat) {i : Nat} (hi : i < count) :
    keepB (input bytes) (output bytes count)
      [((.x26, bytes + 1024 * i), 1024), ((.x28, 0), 1024)]
      (.x25, 0) bytes = true := by
  simp only [keepB, List.all_cons, List.all_nil, Bool.and_true,
    sep25_26, sep25_28, in25, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem row_keep_prefix (bytes count : Nat) {i : Nat} (hi : i < count) :
    keepB (input bytes) (output bytes count)
      [((.x26, bytes + 1024 * i), 1024), ((.x28, 0), 1024)]
      (.x26, 0) bytes = true := by
  simp only [keepB, List.all_cons, List.all_nil, Bool.and_true, sepB_same,
    sep26_28, in26, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  omega

theorem row_keep_prior (bytes count : Nat) {i j : Nat}
    (hi : i < count) (hj : j < i) :
    keepB (input bytes) (output bytes count)
      [((.x26, bytes + 1024 * i), 1024), ((.x28, 0), 1024)]
      (.x26, bytes + 1024 * j) 1024 = true := by
  simp only [keepB, List.all_cons, List.all_nil, Bool.and_true, sepB_same,
    sep26_28, in26, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  omega

end VG.Proof.MlDsa.AArch64.PreparedKey

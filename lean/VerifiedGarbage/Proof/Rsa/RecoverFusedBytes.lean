module

public import VerifiedGarbage.Proof.Rsa.RecoverFused

/-! Eight masked byte shifts implement eight bits of the shared fused model. -/

@[expose] public section
namespace VG.Proof.Rsa.Fused

def byteBits (n b : Nat) : Nat → State → Nat → State × Nat
  | 0, s, w => (s, w)
  | k + 1, s, w => byteBits n b k (step n b (decide (w / 128 % 2 = 1)) s) (2 * w % 256)

theorem byteBits_eight (n b w : Nat) (s : State) :
    byteBits n b 8 s w = (bits n b 8 w s, 0) := by
  have h1 : (2 * w % 256) / 128 % 2 = w / 64 % 2 := by omega
  have h2 : (2 * (2 * w % 256) % 256) / 128 % 2 = w / 32 % 2 := by omega
  have h3 : (2 * (2 * (2 * w % 256) % 256) % 256) / 128 % 2 = w / 16 % 2 := by omega
  have h4 : (2 * (2 * (2 * (2 * w % 256) % 256) % 256) % 256) / 128 % 2 = w / 8 % 2 := by omega
  have h5 : (2 * (2 * (2 * (2 * (2 * w % 256) % 256) % 256) % 256) % 256) / 128 % 2 = w / 4 % 2 := by omega
  have h6 : (2 * (2 * (2 * (2 * (2 * (2 * w % 256) % 256) % 256) % 256) % 256) % 256) / 128 % 2 = w / 2 % 2 := by omega
  have h7 : (2 * (2 * (2 * (2 * (2 * (2 * (2 * w % 256) % 256) % 256) % 256) % 256) % 256) % 256) / 128 % 2 = w / 1 % 2 := by omega
  have h8 : (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * w % 256) % 256) % 256) % 256) % 256) % 256) % 256) % 256) = 0 := by omega
  simp only [byteBits, bits]
  rw [h1, h2, h3, h4, h5, h6, h7, h8]

theorem eight_eval (n b q w : Nat) (hn : 1 < n) (hw : w < 256) :
    bits n b 8 w (eval n b q) = eval n b (q * 256 + w) := by
  have result := bits_eval n b (q * 256 + w) 8 hn
  have initial : (q * 256 + w) / 2 ^ 8 = q := by change (q * 256 + w) / 256 = q; omega
  rw [initial] at result
  have h0 : (q * 256 + w) / 2 ^ 0 % 2 = w / 2 ^ 0 % 2 := by change (q * 256 + w) / 1 % 2 = w / 1 % 2; omega
  have h1 : (q * 256 + w) / 2 ^ 1 % 2 = w / 2 ^ 1 % 2 := by change (q * 256 + w) / 2 % 2 = w / 2 % 2; omega
  have h2 : (q * 256 + w) / 2 ^ 2 % 2 = w / 2 ^ 2 % 2 := by change (q * 256 + w) / 4 % 2 = w / 4 % 2; omega
  have h3 : (q * 256 + w) / 2 ^ 3 % 2 = w / 2 ^ 3 % 2 := by change (q * 256 + w) / 8 % 2 = w / 8 % 2; omega
  have h4 : (q * 256 + w) / 2 ^ 4 % 2 = w / 2 ^ 4 % 2 := by change (q * 256 + w) / 16 % 2 = w / 16 % 2; omega
  have h5 : (q * 256 + w) / 2 ^ 5 % 2 = w / 2 ^ 5 % 2 := by change (q * 256 + w) / 32 % 2 = w / 32 % 2; omega
  have h6 : (q * 256 + w) / 2 ^ 6 % 2 = w / 2 ^ 6 % 2 := by change (q * 256 + w) / 64 % 2 = w / 64 % 2; omega
  have h7 : (q * 256 + w) / 2 ^ 7 % 2 = w / 2 ^ 7 % 2 := by change (q * 256 + w) / 128 % 2 = w / 128 % 2; omega
  simpa only [bits, h0, h1, h2, h3, h4, h5, h6, h7] using result

end VG.Proof.Rsa.Fused

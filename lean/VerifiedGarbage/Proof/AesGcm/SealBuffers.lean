module

-- separate module: locality of the GCM equation is shared by the ARM and x86-64 calling conventions.

public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.AesGcm.Flag
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.Omega

/-! AES-GCM sealing reads the source from the entry memory and writes the
ciphertext and tag to the exit memory. These locality facts depend on the
regions themselves, independently of the ABI and of whether the two payload
pointers coincide. -/
@[expose] public section
namespace VG.Proof.AesGcm.SealBuffers
open VG VG.Spec.Gcm VG.Spec.Aes

abbrev Agree (m₁ m₂ : Mem) (p : Addr) (n : Nat) : Prop :=
  ∀ a, (⟨p,n⟩ : Region).Contains a 1 → m₁ a = m₂ a

/-- The full-tag encryption equation used by the operations on an expanded key. -/
def Equation (ctx nonce aad src dst tag : Addr) (rounds nl al n : Nat) (m out : Mem) : Prop :=
  encryptWith (ctxCiph m ctx rounds) (ctxH m ctx) 16 (bytesAt m nonce nl) (bytesAt m src n)
    (bytesAt m aad al) = (bytesAt out dst n,bytesAt out tag 16)

theorem input_congr {ctx nonce aad src dst tag : Addr} {rounds nl al n : Nat} {m m' out : Mem}
    (hR : rounds≤15) (key : Agree m m' ctx 256) (iv : Agree m m' nonce nl)
    (ad : Agree m m' aad al) (pt : Agree m m' src n) :
    Equation ctx nonce aad src dst tag rounds nl al n m out ↔ Equation ctx nonce aad src dst tag rounds nl al n m' out := by
  unfold Equation
  rw [ctxCiph_congr hR (agree_of key),ctxH_congr (agree_of key),bytesAt_congr (agree_of iv),
    bytesAt_congr (agree_of ad),bytesAt_congr (agree_of pt)]

theorem output_congr {ctx nonce aad src dst tag : Addr} {rounds nl al n : Nat} {m out out' : Mem}
    (ct : Agree out out' dst n) (tg : Agree out out' tag 16) :
    Equation ctx nonce aad src dst tag rounds nl al n m out ↔ Equation ctx nonce aad src dst tag rounds nl al n m out' := by
  unfold Equation
  rw [bytesAt_congr (agree_of ct),bytesAt_congr (agree_of tg)]

theorem keyed {ctx nonce aad src dst tag : Addr} {rounds nl al n : Nat} {m out : Mem} {key : List Byte}
    (hk : KeyRounds m ctx rounds key) (h : Equation ctx nonce aad src dst tag rounds nl al n m out) :
    aesGcmEncrypt key 16 (bytesAt m nonce nl) (bytesAt m src n) (bytesAt m aad al) =
      (bytesAt out dst n,bytesAt out tag 16) := by
  obtain ⟨cipher,hash,_⟩ := keyRounds_ctx hk
  unfold Equation at h
  rwa [cipher,hash,← encrypt_eq] at h

theorem keyRounds_local {m m' : Mem} {ctx : Addr} {rounds : Nat} {key : List Byte}
    (h : Agree m m' ctx 256) (hk : KeyRounds m ctx rounds key) : KeyRounds m' ctx rounds key := by
  obtain ⟨_,_,r⟩ := keyRounds_ctx hk
  refine ⟨hk.1,hk.2.1,?_,(ctxH_congr (agree_of h)).trans hk.2.2.2⟩
  rw [bytesAt_congr (fun i hi => agree_of h i (by rw [← hk.2.1] at hi; rcases r with r|r|r <;> omega))]; exact hk.2.2.1

theorem prepared_local {m m' : Mem} {ctx : Addr} (h : Agree m m' ctx 1032) (valid : PreparedRepr m ctx) :
    PreparedRepr m' ctx :=
  (Flag.flaggedPowers_congr (agree_of h) (show Flag.FlaggedPowers 0 m ctx from ⟨Nat.zero_le _,valid⟩)).2

theorem flag_local {m m' : Mem} {ctx : Addr} (h : Agree m m' ctx 1032) : flagLeak m ctx=flagLeak m' ctx := by
  have eq : m.readW (ctx+1024#64) 64=m'.readW (ctx+1024#64) 64 := by
    apply Mem.readW_congr
    intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact (agree_of h (1024+i) (by omega_using [hi])).symm
  unfold flagLeak powerCount
  rw [show (ctx+1024 : Addr)=ctx+1024#64 from rfl,eq]

end VG.Proof.AesGcm.SealBuffers

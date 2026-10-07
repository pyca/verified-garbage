import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.TableState

/-! Point operations and public counters preserve the scalar's recoded bit table. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

def ScalarBits (K : WinCfg) (base : Addr) (k : Nat) (s : State) : Prop :=
  ∀ i<5*K.J,s.mem (off base (K.bits+i))=if k.testBit i then 1 else 0

theorem ScalarBits.keep {K : WinCfg} {base : Addr} {size k : Nat} {s t : State}
    (hL : SecretLay K size) (hs : Scr s base size) (hb : ScalarBits K base k s)
    {W : List Nat} (hk : CounterKeep K.M base W s t) (hW : ∀ x∈W,x∈writes K) :
    ScalarBits K base k t := by
  intro i hi
  have hn : K.bits+i<2^64 := by have := hL.bits; have := hs.nowrap; omega
  have hv : t.mem (off base (K.bits+i))=s.mem (off base (K.bits+i)) := by
    apply hk.mem
    · intro w hw
      rw [ofs_off0 base hn,hL.n]
      have := hL.bits_w w (hW w hw)
      omega
    · rw [ofs_off0 base hn,hL.n]
      have := hL.bits_tmp
      omega
  exact hv.trans (hb i hi)

end VG.Proof.Ecdh.X86_64.Secret

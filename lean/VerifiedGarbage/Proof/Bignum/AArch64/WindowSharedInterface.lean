module

public import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedCT
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTakeBit
import VerifiedGarbage.Proof.Framework.ModArith

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowShared
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64.WindowFive

theorem window_ok {s : State} {P : Addr} {w : Nat} {mi : BitVec 64}
    {X Xc x E v : Nat} {Q : Prop}
    (hc : TableCtx s P w mi X Xc) (ht : CrtWindowFive.CTab s.mem P w X Q x)
    (hw : 2 ≤ w) (hw' : w < 2^30) (hR : Nat.Coprime (2^(64*w)) X)
    (hy : wv s.mem P (slot w aY) w < X)
    (hyv : Q → wv s.mem P (slot w aY) w % X = x^E * 2^(64*w) % X)
    (hv : v < 32) (hn : word s.mem P (8*Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa code s (WindowPost s P w mi X Xc Q x E v) := by
  have raw : CrtWindowFive.CTab s.mem P w X False 0 := ⟨ht.tab,ht.lt,False.elim⟩
  refine WP.mono (guarded_ok hc raw hw hw' hy hv hn) fun t ⟨ct,yt,vt,nt,bt,ft,kt⟩ => ?_
  have fw := ft.mono (rawWindowRanges_sub w)
  refine ⟨ct,ht.of_win fw hc.scrT.nowrap,yt,?_,ft,kt,nt,bt,?_⟩
  · intro hQ
    have he : wv s.mem P (slot w aY) w % X = x^E * 2^(64*w) % X := hyv hQ
    have ht' : wv s.mem P (slot w (8+v)) w % X = x^v * 2^(64*w) % X := ht.val hQ v hv
    have hm : wv s.mem P (slot w aY) w ^ 32 * wv s.mem P (slot w (8+v)) w % X =
        (x^E * 2^(64*w))^32 * (x^v * 2^(64*w)) % X := by
      rw [Nat.mul_mod, Nat.pow_mod, he, ht', ← Nat.pow_mod, ← Nat.mul_mod]
    have hr : (x^E * 2^(64*w))^32 * (x^v * 2^(64*w)) =
        (x^(32*E+v) * 2^(64*w)) * (2^(64*w))^32 := by
      rw [Nat.mul_pow,Nat.pow_add,← Nat.pow_mul, Nat.mul_comm E 32]
      simp only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    rw [hr] at hm
    exact ModArith.mod_eq_of_mul_mod_eq (hR.pow_left 32)
      ((show wv t.mem P (slot w aY) w * (2^(64*w))^32 % X =
        wv s.mem P (slot w aY) w^32 * wv s.mem P (slot w (8+v)) w % X from vt).trans hm)
  · intro k hk he hj hn' hb
    apply ft.word_eq _ (by have := hdr_lt_slot w 8 hk; have := hc.scrT.nowrap; omega)
    intro r hr
    simp only [rawWindowRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (have := hdr_lt_slot w aAcc hk; simp only; omega)
      | (have := hdr_lt_slot w aTmp hk; simp only; omega)
      | (have := hdr_lt_slot w aY hk; simp only; omega)
      | (have := hdr_lt_slot w Crt.aT hk; simp only; omega)
      | (simp only; omega)

def window : Window := ⟨code,window_ok,code_ct⟩

end VG.Proof.Bignum.AArch64.WindowShared

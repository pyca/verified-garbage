import VerifiedGarbage.Proof.Bignum.X86_64.Words

/-! The reduction block writes one carry word and a separate output range. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Proof.Bignum.X86_64

def BlockOut (B : Addr) (c e n : Nat) (m m' : Mem) : Prop :=
  ∀ x, (ofs B x < c ∨ c + 8 ≤ ofs B x) → (ofs B x < e ∨ e + n ≤ ofs B x) → m' x = m x

theorem BlockOut.refl (B : Addr) (c e n : Nat) (m : Mem) : BlockOut B c e n m m := fun _ _ _ => rfl

theorem BlockOut.first {B : Addr} {c e n : Nat} {m m' : Mem} (h : Outside B c 8 m m') :
    BlockOut B c e n m m' := fun x hx _ => h x hx

theorem BlockOut.second {B : Addr} {c e n : Nat} {m m' : Mem} (h : Outside B e n m m') :
    BlockOut B c e n m m' := fun x _ hx => h x hx

theorem BlockOut.trans {B : Addr} {c e n : Nat} {m m' m'' : Mem}
    (h : BlockOut B c e n m m') (h' : BlockOut B c e n m' m'') : BlockOut B c e n m m'' :=
  fun x hc he => (h' x hc he).trans (h x hc he)

theorem BlockOut.mono {B : Addr} {c e n e' n' : Nat} {m m' : Mem}
    (h : BlockOut B c e n m m') (he : e' ≤ e) (hn : e + n ≤ e' + n') : BlockOut B c e' n' m m' :=
  fun x hc hx => h x hc (by omega)

theorem BlockOut.outside {B : Addr} {c e n a b : Nat} {m m' : Mem}
    (h : BlockOut B c e n m m') (hc : a ≤ c) (hc' : c + 8 ≤ a + b)
    (he : a ≤ e) (he' : e + n ≤ a + b) : Outside B a b m m' :=
  fun x hx => h x (by omega) (by omega)

theorem BlockOut.word {B : Addr} {c e n d : Nat} {m m' : Mem}
    (h : BlockOut B c e n m m') (hc : d + 8 ≤ c ∨ c + 8 ≤ d)
    (he : d + 8 ≤ e ∨ e + n ≤ d) (hd : d + 8 ≤ 2 ^ 64) : word m' B d = word m B d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [ofs_off B (by omega)]; omega)
    (by rw [ofs_off B (by omega)]; omega)).symm).symm

theorem BlockOut.wv {B : Addr} {c e n d k : Nat} {m m' : Mem}
    (h : BlockOut B c e n m m') (hc : d + 8 * k ≤ c ∨ c + 8 ≤ d)
    (he : d + 8 * k ≤ e ∨ e + n ≤ d) (hd : d + 8 * k ≤ 2 ^ 64) : wv m' B d k = wv m B d k :=
  wv_congr fun _ hi => h.word (by omega) (by omega) (by omega)
end VG.Proof.Bignum.X86_64.AdxRotate8

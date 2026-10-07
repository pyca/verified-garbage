import VerifiedGarbage.Proof.RsaPss.X86_64.BufferCopy

/-! Fixed word-sized XORs have the same byte-level effect as MGF1's byte loop. -/
namespace VG.Proof.RsaPss.X86_64
open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)
open VG.Proof.Bignum (off)
open VG.Proof.Pbkdf2.X86_64 (ea_off)

theorem xorScratchWord_ok {u : State} {F S : Addr} (L : Lay u F S)
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem F S V W)
    {a b j : Nat} (ha : a + 8 * j + 8 ≤ oRsa) (hb : b + 8 * j + 8 ≤ oRsa)
    (hsrc : u.gpr .rcx = off S a) (hdst : u.gpr .rdi = off S b) :
    WP isa (.block (xorWord64 j)) u fun t => Lay t F S ∧ Keep [.rax] u t ∧
      Rep t.mem F S (xorV V (a + 8 * j) (b + 8 * j) 8) W := by
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = u.mem.writeW (off S (b + 8 * j))
    (u.mem.readW (off S (a + 8 * j)) 64 ^^^ u.mem.readW (off S (b + 8 * j)) 64)) ?_ rfl)
    fun t ⟨hm, hk⟩ => ?_
  · xrun [xorWord64, VG.Proof.MdStream.X86_64.ea_at, ofInt_nat, hsrc, hdst, off_plus,
      L.sld ha, L.sld hb, L.sst hb]
  have Rt := R.ws L.geo hb (u.mem.readW (off S (a + 8 * j)) 64 ^^^ u.mem.readW (off S (b + 8 * j)) 64)
  rw [← hm] at Rt
  have Rt' : Rep t.mem F S (xorV V (a + 8 * j) (b + 8 * j) 8) W := by
    refine (congrArg (fun V' => Rep t.mem F S V' W) (funext fun x => ?_)).mp Rt
    simp only [stBytes, xorV]
    split
    · rename_i hx
      rw [BitVec.setWidth_eq, BitVec.extractLsb'_xor]
      simp only [Mem.readW, BitVec.setWidth_eq]
      rw [Mem.extractLsb'_read _ _ (by omega : x - (b + 8 * j) < 8),
        Mem.extractLsb'_read _ _ (by omega : x - (b + 8 * j) < 8),
        off_plus, off_plus, R.scr _ (by omega), R.scr _ (by omega)]
      rw [show b + 8 * j + (x - (b + 8 * j)) = x by omega, BitVec.xor_comm]
    · rfl
  exact ⟨L.of_rep R Rt' (hk.gpr (by decide)) hk.2.2, hk, Rt'⟩

theorem xorScratchWords_ok (n : Nat) {u : State} {F S : Addr} (L : Lay u F S)
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem F S V W)
    {a b : Nat} (ha : a + 8 * n ≤ oRsa) (hb : b + 8 * n ≤ oRsa)
    (hsep : a + 8 * n ≤ b ∨ b + 8 * n ≤ a)
    (hsrc : u.gpr .rcx = off S a) (hdst : u.gpr .rdi = off S b) :
    WP isa (.block (xorWords64 n)) u fun t =>
      Lay t F S ∧ Keep [.rax] u t ∧ Rep t.mem F S (xorV V a b (8 * n)) W := by
  induction n with
  | zero =>
    refine WP.block_nil ⟨L, Keep.refl _ _, ?_⟩
    exact (congrArg (fun V' => Rep u.mem F S V' W) (funext fun x => by
      simp only [xorV, Nat.mul_zero, Nat.add_zero]; rw [ifn (by omega)])).mpr R
  | succ n ih =>
    unfold xorWords64
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega) (by omega) (by omega)) fun v ⟨Lv, kv, Rv⟩ => ?_
    refine WP.mono (xorScratchWord_ok Lv Rv (by omega) (by omega)
      ((kv.gpr (by decide)).trans hsrc) ((kv.gpr (by decide)).trans hdst)) fun t ⟨Lt, kt, Rt⟩ => ?_
    refine ⟨Lt, (kv.trans kt).mono (by decide), ?_⟩
    refine (congrArg (fun V' => Rep t.mem F S V' W) (funext fun x => ?_)).mp Rt
    simp only [xorV]
    by_cases hx : b + 8 * n ≤ x ∧ x < b + 8 * n + 8
    · rw [ifp hx, ifn (by omega), ifn (by omega), ifp (by omega)]
      congr 2
      omega
    · rw [ifn hx]
      by_cases hp : b ≤ x ∧ x < b + 8 * n
      · rw [ifp hp, ifp (by omega)]
      · rw [ifn hp, ifn (by omega)]

end VG.Proof.RsaPss.X86_64

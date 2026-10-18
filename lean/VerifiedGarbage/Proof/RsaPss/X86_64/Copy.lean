module

public import VerifiedGarbage.Proof.RsaPss.X86_64.Scan
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS verification on x86-64: copies within the working space

`copyQ a b` copies the 256 bytes at `scratch + a` to `scratch + b` a word at
a time (`copyQ_ok`): the streaming state saved to `oSt2` and restored. And
`copyDb` clears the buffer and copies `DB` to its start (`copyDb_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop seqs)
open VG.Impl.RsaOaep.X86_64 (frameBytes sScr sK sHD sIdx oEm oBuf oSt oDig oW oRsa scr lay)
open VG.Proof.RsaOaep.X86_64 (Lay Rep upd ea_sp ea_at0 ea_ix0 ofNat_add_lit off_plus nW cpV clrV copy_ok
  clearQ_ok stepR_ok byteLoop_ok stBytes sx_lit)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off off_off)
open VG.Proof.Bignum.X86_64 (Scr ofNat_sub_beq wp_upto)

/-- The bytes of a word read from the working space and stored back in it:
the bytes it read. -/
theorem stBytes_read {m : Mem} {S : Addr} {V f : Nat → Byte} {a b : Nat}
    (hr : ∀ i < 8, m (off S (a + i)) = f i) :
    stBytes (m.readW (off S a) 64) b V = fun x => if b ≤ x ∧ x < b + 8 then f (x - b) else V x := by
  funext x
  simp only [stBytes, Mem.readW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]
  split
  · rename_i h
    rw [Mem.extractLsb'_read m (off S a) (j := x - b) (by omega), off_plus, hr _ (by omega)]
  · rfl

/-- The invariant of `copyQ` after `j` words. -/
structure CqI (u₀ : State) (F S : Addr) (V : Nat → Byte) (W : Nat → BitVec 64) (a b j : Nat) (v : State) :
    Prop where
  L : Lay v F S
  keep : Keep [.rax, .r8] u₀ v
  r8 : v.gpr .r8 = BitVec.ofNat 64 (8 * j)
  R : Rep v.mem F S (cpV V (fun i => V (a + i)) b (8 * j)) W

/-- The 256 bytes at `scratch + a` copied to `scratch + b`, apart. -/
theorem copyQ_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {a b : Nat} (ha : a + 256 ≤ oRsa) (hb : b + 256 ≤ oRsa)
    (hab : a + 256 ≤ b ∨ b + 256 ≤ a) (ha31 : a < 2 ^ 31) (hb31 : b < 2 ^ 31) :
    WP isa (copyQ a b) u fun u' => Lay u' F S ∧ Keep [.rsi, .rdi, .rax, .r8] u u' ∧
      Rep u'.mem F S (cpV V (fun i => V (a + i)) b 256) W := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  unfold copyQ
  refine WP.seq (WP.mono (WP.keep [.rsi, .rdi, .r8] (Q := fun v => v.gpr .rsi = off S a ∧ v.gpr .rdi = off S b ∧
      v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl) fun v ⟨⟨h₁, h₂, h₃, hm⟩, hk⟩ => ?_)
  · xrun [scr, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L.rsp,
      L.ld (d := sScr) (by decide), hs, VG.Proof.MlKem.X86_64.sx_ofNat ha31, VG.Proof.MlKem.X86_64.sx_ofNat hb31]
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  refine wp_upto (a := 0) (N := 32) (by decide) (CqI v F S V W a b) ?_ (fun w I => ?_)
    ⟨Lv, Keep.refl _ _, h₃, (congrArg (fun V' => Rep v.mem F S V' W) (funext fun x => by
      simp only [cpV]; rw [ifn (by omega)])).mpr (hm ▸ R)⟩
  · intro j _ hj w I
    have hsi : w.gpr .rsi = off S a := (I.keep.gpr (by decide)).trans h₁
    have hdi : w.gpr .rdi = off S b := (I.keep.gpr (by decide)).trans h₂
    have hrd : ∀ i < 8, w.mem (off S (a + 8 * j + i)) = V (a + (8 * j + i)) := fun i hi => by
      rw [I.R.scr _ (by omega), cpV, ifn (by omega), Nat.add_assoc]
    refine WP.mono (WP.keep [.rax, .r8] (Q := fun w' => w'.zf = some (decide (j + 1 = 32)) ∧
        w'.gpr .r8 = BitVec.ofNat 64 (8 * (j + 1)) ∧
        w'.mem = w.mem.writeW (off S (b + 8 * j)) (w.mem.readW (off S (a + 8 * j)) 64)) ?_ rfl)
      fun w' ⟨⟨hz, h8', hm'⟩, k'⟩ => ⟨hz, ?_⟩
    · xrun [ea_ix0, hsi, hdi, I.r8, off_plus, I.L.sld (d := a + 8 * j) (by omega),
        I.L.sst (d := b + 8 * j) (by omega), ofNat_add_lit, sx_lit 256 (by decide),
        ofNat_sub_beq (show 8 * j + 8 < 2 ^ 64 by omega) (show 256 < 2 ^ 64 by decide)]
      exact ⟨by simp only [decide_eq_decide]; omega, congrArg _ (by omega)⟩
    · have R' := I.R.ws I.L.geo (o := b + 8 * j) (w := 64) (by omega) (w.mem.readW (off S (a + 8 * j)) 64)
      rw [← hm', stBytes_read hrd] at R'
      have R'' : Rep w'.mem F S (cpV V (fun i => V (a + i)) b (8 * (j + 1))) W := by
        refine (congrArg (fun V' => Rep w'.mem F S V' W) (funext fun x => ?_)).mp R'
        simp only [cpV]
        by_cases h1 : b + 8 * j ≤ x ∧ x < b + 8 * j + 8
        · rw [ifp h1, ifp (by omega)]; exact congrArg V (by omega)
        · rw [ifn h1]
          by_cases h2 : b ≤ x ∧ x < b + 8 * j
          · rw [ifp h2, ifp (by omega)]
          · rw [ifn h2, ifn (by omega)]
      exact ⟨I.L.of_rep I.R R'' (k'.gpr (by decide)) k'.2.2, (I.keep.trans k').mono (by decide), h8', R''⟩
  · have R' := I.R
    rw [show 8 * 32 = 256 from rfl] at R'
    exact ⟨I.L, (hk.trans I.keep).mono (by decide), R'⟩

/-- The buffer's 2048 bytes cleared, then `DB` (the `db` bytes at `e`)
copied to its start; `rcx` the buffer. -/
theorem copyDb_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {e db : Nat} (he : W 33 = off S e) (hdb : W 44 = BitVec.ofNat 64 db)
    (hdb1 : 1 ≤ db) (hfit : e + db ≤ oBuf) :
    WP isa copyDb u fun u' => Lay u' F S ∧ Keep [.rcx, .rsi, .r10, .rax, .r8] u u' ∧
      u'.gpr .rcx = off S oBuf ∧ Rep u'.mem F S (cpV (clrV V oBuf 2048) (fun i => V (e + i)) oBuf db) W := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  have c3 : oBuf = 1024 := rfl
  have c5 : oRsa = 8192 := rfl
  unfold copyDb seqs seqs seqs
  refine WP.seq (WP.mono (WP.keep [.rcx, .rax, .r8] (Q := fun v => v.gpr .rcx = off S oBuf ∧ v.gpr .rax = 0 ∧
      v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl) fun v ⟨⟨h₁, h₂, h₃, hm⟩, hk⟩ => ?_)
  · xrun [scr, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L.rsp,
      L.ld (d := sScr) (by decide), hs, VG.Proof.MlKem.X86_64.sx_ofNat (show oBuf < 2 ^ 31 by decide)]
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  refine WP.seq (WP.mono (clearQ_ok Lv (hm ▸ R) (o := oBuf) (n := 2048) (by decide) (by decide) (by decide)
    (by decide) h₁ h₂ h₃) fun w ⟨Lw, kw, Rw⟩ => ?_)
  have hcw : w.gpr .rcx = off S oBuf := (kw.gpr (by decide)).trans h₁
  refine WP.seq (WP.mono (WP.keep [.rsi, .r10, .r8] (Q := fun x => x.gpr .rsi = off S e ∧
      x.gpr .r10 = BitVec.ofNat 64 db ∧ x.gpr .r8 = BitVec.ofNat 64 0 ∧ x.mem = w.mem) ?_ rfl)
    fun x ⟨⟨a₁, a₂, a₃, hmx⟩, kx⟩ => ?_)
  · xrun [ea_sp, Lw.rsp, Lw.ld (d := sEb) (by decide), Lw.ld (d := sDb) (by decide),
      Rw.rd (d := sEb) 33 rfl (by decide), Rw.rd (d := sDb) 44 rfl (by decide), he, hdb]
  have Lx : Lay x F S := Lw.congr (kx.gpr (by decide)) kx.2.2 (by rw [hmx])
  have hcx : x.gpr .rcx = off S oBuf := (kx.gpr (by decide)).trans hcw
  refine WP.mono (copy_ok Lx (hmx ▸ Rw) (d := .rcx) (by decide) (p := off S e) (o := oBuf) (disp := 0) (n := db)
    (stepR_ok (by omega) x (show Reg.r10 ∉ [Reg.rax, .r8] by decide) (by decide) a₂) hdb1
    (by omega) a₁ hcx a₃
    (fun i hi => by rw [off_plus]; exact Lx.sld8 (by omega))
    (fun i hi j hj => by
      rw [off_plus]; exact Offset.add_ofNat_ne S (by omega) (by omega) (by omega)))
    fun y ⟨Ly, ky, Ry⟩ => ⟨Ly, (hk.trans (kw.trans (kx.trans ky))).mono (by decide),
      (ky.gpr (by decide)).trans hcx, ?_⟩
  refine (congrArg (fun V' => Rep y.mem F S V' W) (funext fun z => ?_)).mp Ry
  simp only [cpV, Nat.add_zero]
  split
  · rw [hmx, off_plus, Rw.scr _ (by omega), clrV, ifn (by omega)]
  · rfl

end VG.Proof.RsaPss.X86_64

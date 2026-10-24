module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.KSOps
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on PPC64LE: comparisons of arrays

`ltS_vp`: the header word `d` := `[a] < [b]`, the borrow of `[a] − [b]` into
the array `aTmp`, which no stage keeps. `andCmp_vp`: the header word `d` :=
the header words `a` and `b` and'ed, and into `r0`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE VG.Proof.Mont
open VG.Proof.Rsa.KeyWorkspace (num slot)
open VG.Proof.Rsa.PPC64LE.Keys (Ws opRegs sub3_ok stBorrow_ok andS_ok)
open VG.Impl.Rsa.PPC64LE.Keys (seqs sub3 stBorrow andS)
open VG.Impl.Dsa.PPC64LE.Generation

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- `[a] − [b]` into `aTmp`: the borrow, `[a] < [b]`, in `r9`. -/
theorem sub3b_vp {a b : Nat} (cert : CertK (sub3 aTmp a b)) (ha : a ∈ c.live) (hb : b ∈ c.live)
    (hta : aTmp ≠ a) (htb : aTmp ≠ b) (htl : aTmp ∉ c.live) :
    VP (KSt G c X) (sub3 aTmp a b)
      (fun σ t => KSt G c X σ t ∧ (t.gpr .r9).toNat = if c.A a < c.A b then 1 else 0) := by
  refine ks_vp cert (fun σ s h => ⟨h.1.1, h.2⟩) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  have hw := h.ws kr
  have va := h.arrs.get ha
  have vb := h.arrs.get hb
  refine h.ksOp (P := fun t => num t.mem G.KB G.w aTmp + num s.mem G.KB G.w b =
      num s.mem G.KB G.w a + 2 ^ (32 * G.w) * (t.gpr .r9).toNat ∧ (t.gpr .r9).toNat ≤ 1) rfl
    ((sub3_ok hw (by decide) (h.liveOk a ha) (h.liveOk b hb) (by decide) hta htb).mono
      fun t ⟨w, k, v, br, r⟩ => ⟨w, k, ⟨v, br⟩, r⟩)
    fun t k ⟨v, br⟩ R sp f => ⟨⟨⟨(h.of_op R sp f (by decide) k rfl).mono (fun o ho => ⟨ho, rfl⟩)
      (fun y hy => hy) (fun j hj => ⟨List.mem_cons_of_mem _ hj,
        VG.Proof.Rsa.KeyWorkspace.upd_ne _ _ fun e => htl (e ▸ hj)⟩) (fun d hd => ⟨hd, rfl⟩), x⟩,
      kr.of_keep R⟩, ?_⟩
  simp only [GP.ksState, State.withRegions_mem, State.withRegions_gpr] at v br
  rw [va, vb] at v
  have lt : num t.mem G.KB G.w aTmp < 2 ^ (32 * G.w) := val32_lt _ _ _ _
  have blt : c.A b < 2 ^ (32 * G.w) := vb ▸ val32_lt _ _ _ _
  generalize 2 ^ (32 * G.w) = M at v lt blt
  have m1 : M * 1 = M := Nat.mul_one M
  have m0 : M * 0 = 0 := Nat.mul_zero M
  rcases (by omega : (t.gpr .r9).toNat = 0 ∨ (t.gpr .r9).toNat = 1) with e | e <;> rw [e] at v ⊢ <;> split <;> omega

/-- The header word `d` := `[a] < [b]`. -/
theorem ltS_vp {d a b : Nat} (c1 : CertK (sub3 aTmp a b)) (c2 : CertK (.block (stBorrow d)))
    (ha : a ∈ c.live) (hb : b ∈ c.live) (hta : aTmp ≠ a) (htb : aTmp ≠ b) (htl : aTmp ∉ c.live)
    (hd : KlsOk d) :
    VP (KSt G c X) (seqs (ltS d a b))
      (KSt G { c with KV := KU c.KV d (if c.A a < c.A b then 1 else 0), kls := d :: c.kls } X) := by
  rw [show seqs (ltS d a b) = .seq (sub3 aTmp a b) (.block (stBorrow d)) from rfl]
  refine VP.seq (sub3b_vp c1 ha hb hta htb htl) ?_
  refine ks_vp c2 (fun σ s h => ⟨h.1.1.1, h.1.2⟩) fun σ s ⟨⟨⟨h, x⟩, kr⟩, b9⟩ => ?_
  have hw := h.ws kr
  refine h.ksOp (js := []) (ds := [d]) (P := fun t => slot t.mem G.KB d = (s.gpr .r9).toNat) rfl
    (by rw [← List.append_nil (stBorrow d)]
        exact stBorrow_ok hw hd.1 (by show (s.gpr .r9).toNat ≤ 1; rw [b9]; split <;> decide)
          fun t w k v r => WP.block_nil ⟨w, k, v, r⟩)
    fun t k v R sp f => ⟨⟨h.of_opS R sp f hd k (by
      simp only [GP.ksState, State.withRegions_mem] at v; rw [v, b9]), x⟩, kr.of_keep R⟩

/-- The header word `d` := the header words `a` and `b` (each 0 or 1)
and'ed, and `r0` := it. -/
theorem andCmp_vp {d a b : Nat} (cert : CertK (.block (andS d a b ++ ([.load .w .r0 .r31 d] : List Instr))))
    (hd : KlsOk d) (ha : a ∈ c.kls) (hb : b ∈ c.kls) (ba : c.KV a ≤ 1) (bb : c.KV b ≤ 1) :
    VP (KSt G c X) (.block (andS d a b ++ ([.load .w .r0 .r31 d] : List Instr)))
      (fun σ t => KSt G { c with KV := KU c.KV d (if c.KV a = 1 ∧ c.KV b = 1 then 1 else 0), kls := d :: c.kls } X σ t ∧
        isa.eval (.zero .d .r0) t = some (decide ¬(c.KV a = 1 ∧ c.KV b = 1))) := by
  refine ks_vp cert (fun σ s h => ⟨h.1.1, h.2⟩) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  have hw := h.ws kr
  have va : slot (G.ksState s).mem G.KB a = c.KV a := h.ksl a ha
  have vb : slot (G.ksState s).mem G.KB b = c.KV b := h.ksl b hb
  have hz : 160 ≤ kz G.pLen := hw.hdr_le
  have d4 : d + 4 ≤ 160 := hd.1
  refine h.ksOp (js := []) (ds := [d]) (ws := opRegs ++ [.r0]) (P := fun t =>
      slot t.mem G.KB d = (if c.KV a = 1 ∧ c.KV b = 1 then 1 else 0) ∧
      isa.eval (.zero .d .r0) t = some (decide ¬(c.KV a = 1 ∧ c.KV b = 1))) rfl ?_
    fun t k ⟨e, z⟩ R sp f => ⟨⟨⟨h.of_opS R sp f hd k e, x⟩, kr.of_keep R⟩, z⟩
  refine andS_ok hw hd.1 (h.kslOk a ha).1 (h.kslOk b hb).1 (by rw [va]; exact ba) (by rw [vb]; exact bb)
    fun t₁ w₁ k₁ v₁ R₁ => ?_
  have hx : WP isa (.block [.load .w .r0 .r31 d]) t₁ fun t₂ =>
      (t₂.gpr .r0 = (t₁.mem.readW (t₁.gpr .r31 + BitVec.ofNat 64 d) 32).setWidth 64 ∧ t₂.mem = t₁.mem) ∧
        VG.Proof.Bignum.PPC64LE.Keep [.r0] t₁ t₂ :=
    WP.wr (exec_load_w (show Reg.r31 ≠ .r0 by decide) (show d < 2 ^ 15 by omega)
      (by rw [w₁.r31]; exact w₁.scr.ld (show d + 4 ≤ kz G.pLen by omega))) fun t₂ u sp lr => WP.block_nil
      ⟨⟨u.gpr, u.mem⟩, ⟨fun r hr => u.other r (by simpa using hr), u.rd, u.wr, sp, lr⟩⟩
  refine WP.mono hx fun t₂ ⟨⟨u0, m2⟩, k2⟩ => ?_
  have v : slot t₂.mem G.KB d = (if c.KV a = 1 ∧ c.KV b = 1 then 1 else 0) := by rw [m2, v₁, va, vb]
  refine ⟨w₁.of_keep k2, by rw [m2]; exact k₁, ⟨v, ?_⟩, R₁.trans k2⟩
  have r : t₂.gpr .r0 = BitVec.ofNat 64 (if c.KV a = 1 ∧ c.KV b = 1 then 1 else 0) := by
    have rd : (t₁.mem.readW (t₁.gpr .r31 + BitVec.ofNat 64 d) 32).toNat =
        (if c.KV a = 1 ∧ c.KV b = 1 then 1 else 0) := by
      rw [w₁.r31]; have := v; rw [m2] at this; exact this
    refine BitVec.eq_of_toNat_eq ?_
    rw [u0, VG.Proof.Bignum.PPC64LE.toNat_ext32, rd, BitVec.toNat_ofNat]
    split <;> rfl
  rw [eval_zero_ofNat _ _ (by split <;> decide) r]
  by_cases hc : c.KV a = 1 ∧ c.KV b = 1 <;> simp [hc]

end

end VG.Proof.Dsa.PPC64LE.Gen

module

public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Power
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # DSA parameter search on RISC-V: one `h` of the generator search

As on PPC64LE (`Proof/Dsa/PPC64LE/Gen/GCmp.lean` and `GStep.lean`).
`gStep` (`gStep_vp`): `h`, the `pLen` bytes at the address in `fH`, into
array `aH` of the key working space (zeroed first); unless `1 < h < p − 1`
(`ltS_vp`, `andCmp_vp`), nothing more; else `g = h^e mod p` by the power in
the P space (`power_vp`), and if `g > 1`, `g` big-endian at `sG`
(`gStore_vp`) and `fG` := 1. The `h` bytes are the caller's: the octets at
`H`, apart from `scratch` and the stack, as they were on entry (`σ`), which
every state of the search keeps.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.Mont
open VG.Proof.Rsa.RISCV64.Keys (Ws arr num slot S opRegs)
open VG.Impl.Rsa.RISCV64.Keys (seqs sub3 stBorrow andS load)
open VG.Impl.Dsa.RISCV64.ParameterSearch

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- Bytes apart from `scratch` and the stack, as on entry. -/
theorem SS.srcAt {σ s : State} {c' : Cfg} (h : SS G STK0 σ c' s) {H : Addr} {n : Nat}
    (hR : ∀ i < n, InRegions (σ.rd ++ σ.wr) (off H i) 1) (d1 : Region.Disjoint ⟨H, n⟩ G.rScr)
    (d2 : Region.Disjoint ⟨H, n⟩ (rBelow σ STK0)) (hfit : H.toNat + n ≤ 2 ^ 64) :
    (∀ i < n, InRegions (s.rd ++ s.wr) (off H i) 1) ∧
      Spec.Rsa.bytesAt s.mem H n = Spec.Rsa.bytesAt σ.mem H n := by
  have gi := h.gi
  refine ⟨fun i hi => by rw [gi.rd, gi.wr]; exact hR i hi, ?_⟩
  refine VG.Proof.Dsa.Generation.frame_bytesAt gi.frame (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact d1
  · exact d2

/-- Array `j`, zero, := the `n` bytes `bs` at `a0` (`a1 = n`), readable and
apart from the key working space. -/
theorem loadK_vp {j n : Nat} {P : Addr} {bs : List Byte} (cert : CertL j)
    (hj : j < nArrs) (hjl : j ∈ c.live) (hj0 : c.A j = 0) (hn0 : 0 < n) (hnw : n ≤ 8 * G.w)
    (hsrc : ∀ σ s, St G c X σ s → (∀ i < n, InRegions (s.rd ++ s.wr) (off P i) 1) ∧
      Region.Disjoint ⟨P, n⟩ G.rK ∧ P.toNat + n ≤ 2 ^ 64 ∧ Spec.Rsa.bytesAt s.mem P n = bs) :
    VP (fun σ s => KSt G c X σ s ∧ s.gpr .a0 = P ∧ s.gpr .a1 = BitVec.ofNat 64 n)
      (load j .a0 .a1)
      (KSt G { c with A := KU c.A j (Spec.Dsa.decodeBE bs), live := j :: c.live } X) := by
  refine VP.pub (G := G) (fun σ s hs => ⟨hs.1.1.1.gi.s6, by rw [hs.1.1.1.gi.sp, ← hs.1.1.1.gi.hG]; rfl⟩)
    [.s9, .s10, .s11, .a0, .a1] cert
    (fun σ₁ σ₂ s₁ s₂ ⟨⟨_, a⟩, a0, a1⟩ ⟨⟨_, b⟩, b0, b1⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [a.s9, b.s9]
      · rw [a.s10, b.s10]
      · rw [a.s11, b.s11]
      · rw [a0, b0]
      · rw [a1, b1]) fun σ s ⟨⟨⟨h, x⟩, kr⟩, p0, p1⟩ => ?_
  obtain ⟨hR, sep, fit, b⟩ := hsrc σ s ⟨h, x⟩
  have hw := h.ws kr
  have z : num s.mem G.KB G.w j = 0 := by rw [h.arrs j hjl, hj0]
  have hc : ∀ i < n, (⟨P, n⟩ : Region).Contains (off P i) 1 := fun i hi =>
    Offset.contains_base _ (by omega) (by omega)
  refine h.ksOp kr (js := [j]) (ds := []) (by simpa using hj) (by simp)
    (P := fun t => num t.mem G.KB G.w j = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P n))
    ((VG.Proof.Rsa.RISCV64.Keys.load_ok hw hj (by decide) (by decide) p0 p1 hn0 hnw hR
      (fun i hi x hx e => by subst e; exact absurd (past_of_disjoint' sep (hc i hi)) (Nat.not_le.mpr hx)) z).mono
      fun t ⟨w, k, v, r, _⟩ => ⟨w, k, v, r⟩)
    fun t k v R sp f => ?_
  have vw : num t.mem G.KB G.w j = Spec.Dsa.decodeBE bs := by rw [v, b, VG.Proof.Dsa.decodeBE_os2ip]
  exact ⟨⟨h.of_op R sp f hj k vw, x⟩, kr.of_keep R⟩

/-- `h`'s pointer, from the header word `fH`, and its length, in the key working space. -/
theorem hPtrK_vp {H : Addr} (hH : fH ∈ c.LS) (hHv : c.V fH = H) :
    VP (KSt G c X) (.block [ld .a0 fH, .li .a1 G.pLen])
      (fun σ s => KSt G c X σ s ∧ s.gpr .a0 = H ∧ s.gpr .a1 = BitVec.ofNat 64 G.pLen) := by
  refine VP.pub (SS.pub fun σ s h => h.1.1) [] ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6])
    (.block [ld .a0 fH, .li .a1 G.pLen]), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
    fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  have l := h.lens
  have p11 : G.pLen < 2048 := by rcases l with e | e | e <;> rw [e] <;> decide
  refine h.ldK (o := fH) (by decide) (by decide) ((h.gi.slotV hH).trans hHv) (t := .a0) (by decide)
    fun s₁ h₁ u₁ => wp_li p11 fun t u => WP.block_nil ?_
  have K : Keep [.a0, .a1] s t := ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u.other _ hr.2, u₁.other _ hr.1], by rw [u.rd, u₁.rd], by rw [u.wr, u₁.wr]⟩
  refine ⟨⟨⟨h₁.of_upd u (by decide), x⟩, kr.of_keep K⟩, ?_, u.gpr⟩
  rw [u.other _ (by decide), u₁.gpr]

/-- `[a] − [b]` into `aTmp`: the borrow, `[a] < [b]`, in `t4`. -/
theorem sub3b_vp {a b : Nat} (cert : CertK (sub3 aTmp a b)) (ha : a ∈ c.live) (hb : b ∈ c.live)
    (hta : aTmp ≠ a) (htb : aTmp ≠ b) (htl : aTmp ∉ c.live) :
    VP (KSt G c X) (sub3 aTmp a b)
      (fun σ t => KSt G c X σ t ∧ (t.gpr .t4).toNat = if c.A a < c.A b then 1 else 0) := by
  refine ks_vp cert (fun σ s h => ⟨h.1.1, h.2⟩) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  have hw := h.ws kr
  have va := h.arrs a ha
  have vb := h.arrs b hb
  refine h.ksOp kr (js := [aTmp]) (ds := []) (by simp; decide) (by simp)
    (P := fun t => num t.mem G.KB G.w aTmp + num s.mem G.KB G.w b =
      num s.mem G.KB G.w a + 2 ^ (64 * G.w) * (t.gpr .t4).toNat ∧ (t.gpr .t4).toNat ≤ 1)
    ((VG.Proof.Rsa.RISCV64.Keys.sub3_ok hw (by decide) (h.liveOk a ha) (h.liveOk b hb) (by decide) hta htb).mono
      fun t ⟨w, k, v, br, r⟩ => ⟨w, k, ⟨v, br⟩, r⟩)
    fun t k ⟨v, br⟩ R sp f => ⟨⟨⟨(h.of_op R sp f (by decide) k rfl).mono (fun o ho => ⟨ho, rfl⟩)
      (fun y hy => hy) (fun j hj => ⟨List.mem_cons_of_mem _ hj, KU_ne _ _ fun e => htl (e ▸ hj)⟩)
      (fun d hd => ⟨hd, rfl⟩), x⟩, kr.of_keep R⟩, ?_⟩
  rw [va, vb] at v
  have lt := num_lt t.mem G.KB G.w aTmp
  have blt : c.A b < 2 ^ (64 * G.w) := vb ▸ num_lt _ _ _ _
  generalize 2 ^ (64 * G.w) = M at v lt blt
  have m1 : M * 1 = M := Nat.mul_one M
  have m0 : M * 0 = 0 := Nat.mul_zero M
  rcases (by omega : (t.gpr .t4).toNat = 0 ∨ (t.gpr .t4).toNat = 1) with e | e <;> rw [e] at v ⊢ <;>
    split <;> omega

/-- The key slot `d` := `[a] < [b]`. -/
theorem ltS_vp {d a b : Nat} (c1 : CertK (sub3 aTmp a b)) (c2 : CertK (.block (stBorrow d)))
    (ha : a ∈ c.live) (hb : b ∈ c.live) (hta : aTmp ≠ a) (htb : aTmp ≠ b) (htl : aTmp ∉ c.live)
    (hd : KlsOk d) :
    VP (KSt G c X) (seqs (ltS d a b))
      (KSt G { c with KV := KU c.KV d (if c.A a < c.A b then 1 else 0), kls := d :: c.kls } X) := by
  rw [show seqs (ltS d a b) = .seq (sub3 aTmp a b) (.block (stBorrow d)) from rfl]
  refine VP.seq (sub3b_vp c1 ha hb hta htb htl) ?_
  refine ks_vp c2 (fun σ s h => ⟨h.1.1.1, h.1.2⟩) fun σ s ⟨⟨⟨h, x⟩, kr⟩, b4⟩ => ?_
  have hw := h.ws kr
  refine h.ksOp kr (js := []) (ds := [d]) (by simp) (by simpa using hd.1)
    (P := fun t => slot t.mem G.KB d = (s.gpr .t4).toNat)
    ((VG.Proof.Rsa.RISCV64.Keys.stBorrow_ok hw hd.1 hd.2).mono fun t ⟨w, k, v, r⟩ => ⟨w, k, v, r⟩)
    fun t k v R sp f => ⟨⟨h.of_opS R sp f hd k (by rw [v, b4]), x⟩, kr.of_keep R⟩

/-- The key slot `d` := the key slots `a` and `b` (each 0 or 1) and'ed, and
`t2` := it. -/
theorem andCmp_vp {d a b : Nat} (cert : CertK (.block (andS d a b ++ ([.load .d .t2 .s11 d] : List Instr))))
    (hd : KlsOk d) (ha : a ∈ c.kls) (hb : b ∈ c.kls) (ba : c.KV a ≤ 1) (bb : c.KV b ≤ 1) :
    VP (KSt G c X) (.block (andS d a b ++ ([.load .d .t2 .s11 d] : List Instr)))
      (fun σ t =>
        KSt G { c with KV := KU c.KV d (if c.KV a = 1 ∧ c.KV b = 1 then 1 else 0), kls := d :: c.kls } X σ t ∧
        isa.eval (.zero .t2) t = some (decide ¬(c.KV a = 1 ∧ c.KV b = 1))) := by
  refine ks_vp cert (fun σ s h => ⟨h.1.1, h.2⟩) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  have hw := h.ws kr
  have va : slot s.mem G.KB a = c.KV a := h.ksl a ha
  have vb : slot s.mem G.KB b = c.KV b := h.ksl b hb
  have hz := hw.hdr_le
  have d8 := hd.1
  have e1 : VG.Proof.Rsa.RISCV64.Keys.hdr = 256 := VG.Proof.Rsa.RISCV64.Keys.hdr_eq
  have e2 : VG.Impl.Rsa.RISCV64.Keys.hdr = 256 := VG.Proof.Rsa.RISCV64.Keys.hdr_eq
  have ab : slot s.mem G.KB a * slot s.mem G.KB b = if c.KV a = 1 ∧ c.KV b = 1 then 1 else 0 := by
    rw [va, vb]
    rcases (by omega : c.KV a = 0 ∨ c.KV a = 1) with e | e <;>
      rcases (by omega : c.KV b = 0 ∨ c.KV b = 1) with f | f <;> simp [e, f]
  refine h.ksOp kr (js := []) (ds := [d]) (ws := opRegs ++ [.t2]) (by simp) (by simpa using hd.1)
    (P := fun t => slot t.mem G.KB d = (if c.KV a = 1 ∧ c.KV b = 1 then 1 else 0) ∧
      isa.eval (.zero .t2) t = some (decide ¬(c.KV a = 1 ∧ c.KV b = 1))) ?_
    fun t k ⟨e, z⟩ R sp f => ⟨⟨⟨h.of_opS R sp f hd k e, x⟩, kr.of_keep R⟩, z⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rsa.RISCV64.Keys.andS_ok hw hd.1 hd.2 (h.kslOk a ha).1 (h.kslOk a ha).2
    (h.kslOk b hb).1 (h.kslOk b hb).2 (by rw [va]; exact ba) (by rw [vb]; exact bb)) fun t₁ ⟨w₁, k₁, v₁, R₁⟩ => ?_
  refine wp_ld (off := d) (a := off G.KB d) (by simp only [KlsOk, VG.Impl.Rsa.RISCV64.Keys.hdr] at hd; omega)
    (by rw [w₁.s11]) (w₁.scr.al8 (by omega) hd.2) (w₁.scr.ld (by omega)) fun t₂ u => WP.block_nil ?_
  have k2 : Keep [.t2] t₁ t₂ := ⟨fun r hr => u.other r (by simpa using hr), u.rd, u.wr⟩
  have v : slot t₂.mem G.KB d = (if c.KV a = 1 ∧ c.KV b = 1 then 1 else 0) := by rw [u.mem, v₁, ab]
  refine ⟨w₁.of_keep k2, by rw [u.mem]; exact k₁, ⟨v, ?_⟩, R₁.trans k2⟩
  have r : t₂.gpr .t2 = BitVec.ofNat 64 (if c.KV a = 1 ∧ c.KV b = 1 then 1 else 0) := by
    refine BitVec.eq_of_toNat_eq ?_
    rw [u.gpr, BitVec.toNat_ofNat]
    have : (t₁.mem.readW (off G.KB d) 64).toNat = (if c.KV a = 1 ∧ c.KV b = 1 then 1 else 0) := by
      have := v; rw [u.mem] at this; exact this
    rw [this]; split <;> rfl
  rw [eval_zero_ofNat _ _ (by split <;> decide) r]
  by_cases hc : c.KV a = 1 ∧ c.KV b = 1 <;> simp [hc]

end

/-- The stage after an `h` (`hv`), from `p` (`pv`) and the exponent (`ev`). -/
def gOut (c : Cfg) (G : GP) (hv pv ev : Nat) : Cfg :=
  if 1 < hv ∧ hv < pv - 1 ∧ 1 < hv ^ ev % pv then
    ({ c with cl := (sG, Spec.Rsa.i2osp (hv ^ ev % pv) G.pLen) :: c.cl }).setV fG 1
  else c

/-- Simplifies the arrays and key slots of `gStep`'s stages. -/
syntax "g_simp" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| g_simp $[$loc]?) => `(tactic| simp only [KU, aPm1, aH, aOne, aZero, aTmp, slLo, slHi,
    Nat.reduceEqDiff, ↓reduceIte] $[$loc]?)

section
variable {G : GP} {c : Cfg} {X : State → Prop}

theorem varOk_fG {G : GP} : VarOk G fG := by
  refine ⟨by decide, by decide, by decide, fun p hp => ?_⟩
  simp only [fixedWords, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)

/-- A stage with more arrays and key slots than `c₀`, and the same header
words and claims, is `c₀`'s. -/
theorem SS.back {σ s : State} {c' c₀ : Cfg} (h : SS G STK0 σ c' s) (hk : c₀.kls = []) (eV : c'.V = c₀.V)
    (eLS : c'.LS = c₀.LS) (ecl : c'.cl = c₀.cl) (eA : ∀ j ∈ c₀.live, j ∈ c'.live ∧ c'.A j = c₀.A j) :
    SS G STK0 σ c₀ s :=
  h.mono (fun o ho => ⟨eLS ▸ ho, by rw [eV]⟩) (fun y hy => ecl ▸ hy) eA (fun d hd => by simp [hk] at hd)

theorem beq_zero_of_iff {x : BitVec 64} {p : Prop} [Decidable p] (h : x = 0 ↔ p) : (x == 0) = decide p := by
  by_cases hp : p
  · rw [decide_eq_true hp]; exact beq_iff_eq.mpr (h.mpr hp)
  · rw [decide_eq_false hp]; exact beq_false_of_ne fun e => hp (h.mp e)

theorem ite01_eq_one (p : Prop) [Decidable p] : ((if p then 1 else 0) = 1) ↔ p := by
  by_cases hp : p <;> simp [hp]

theorem ite01_le (p : Prop) [Decidable p] : (if p then 1 else 0) ≤ 1 := by
  by_cases hp : p <;> simp [hp]

/-- One `h`, the `pLen` octets `hb` at `H`, the address in `fH`: the stage
`gOut`. -/
theorem gStep_vp {g : Geo} (hg : g.pLen = G.pLen) (hgq : g.qLen = G.qLen) (cert : CertC G.pLen G.qLen)
    {pv ev : Nat} {H : Addr} {hb : List Byte} (hM : aPm1 ∈ c.live) (hMv : c.A aPm1 = pv - 1)
    (hO : aOne ∈ c.live) (hOv : c.A aOne = 1) (hZ : aZero ∈ c.live) (hZv : c.A aZero = 0)
    (hHl : aH ∉ c.live) (hTl : aTmp ∉ c.live) (hkls : c.kls = [])
    (hPc : (sPBE, Spec.Rsa.i2osp pv G.pLen) ∈ c.cl) (hpv : pv < 256 ^ G.pLen) (hp2 : 2 ≤ pv) (hpo : pv % 2 = 1)
    (hEc : (sE, Spec.Rsa.i2osp ev (eBytes G.pLen G.qLen)) ∈ c.cl) (hev : ev < 256 ^ eBytes G.pLen G.qLen)
    (hcl : ∀ x ∈ c.cl, Apart pB (pZ G.pLen) x ∧ Apart sG G.pLen x)
    (hH : fH ∈ c.LS) (hHv : c.V fH = H)
    (hsrc : ∀ σ, X σ → (∀ i < G.pLen, InRegions (σ.rd ++ σ.wr) (off H i) 1) ∧
      Region.Disjoint ⟨H, G.pLen⟩ G.rScr ∧ Region.Disjoint ⟨H, G.pLen⟩ (rBelow σ STK0) ∧
      H.toNat + G.pLen ≤ 2 ^ 64 ∧ Spec.Rsa.bytesAt σ.mem H G.pLen = hb) :
    VP (St G c X) g.gStep (St G (gOut c G (Spec.Dsa.decodeBE hb) pv ev) X) := by
  by_cases l : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384
  swap
  · exact VP.of_false fun σ s h => l h.1.lens
  have src : ∀ (c' : Cfg) σ s, St G c' X σ s → (∀ i < G.pLen, InRegions (s.rd ++ s.wr) (off H i) 1) ∧
      Region.Disjoint ⟨H, G.pLen⟩ G.rScr ∧ H.toNat + G.pLen ≤ 2 ^ 64 ∧ Spec.Rsa.bytesAt s.mem H G.pLen = hb :=
    fun c' σ s ⟨h, x⟩ => by
      obtain ⟨hR, d1, d2, fit, b⟩ := hsrc σ x
      obtain ⟨r, e⟩ := h.srcAt hR d1 d2 fit
      exact ⟨r, d1, fit, e.trans b⟩
  unfold Geo.gStep
  rw [hg, hgq]
  generalize hhv : Spec.Dsa.decodeBE hb = hv
  have kc : ∀ (v : Nat), ∀ j ∈ c.live, j ∈ aH :: aH :: c.live ∧ KU (KU c.A aH (c.A aZero)) aH v j = c.A j :=
    fun v j hj => ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj), by
      have : j ≠ aH := fun e => hHl (e ▸ hj)
      rw [KU_ne _ _ this, KU_ne _ _ this]⟩
  -- Into the key working space; `aH` := 0, then `h`.
  refine VP.seq ksEnter_vp ?_
  refine VP.seq (copy_vp (o := aH) (a := aZero) ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64
    (Taint.ofRegs [.s6, .s9, .s10, .s11]) (VG.Impl.Rsa.RISCV64.Keys.copy aH aZero), by kernel_rfl⟩
    (by decide) hZ (by decide)) ?_
  refine VP.seq (hPtrK_vp hH hHv) ?_
  refine VP.seq (loadK_vp (j := aH) (n := G.pLen) (bs := hb) ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64
      (Taint.ofRegs [.s6, .s9, .s10, .s11, .a0, .a1]) (load aH .a0 .a1), by kernel_rfl⟩
    (by decide) List.mem_cons_self (by g_simp; exact hZv)
    (by rcases l with e | e | e <;> rw [e] <;> decide)
    (by simp only [GP.w]; rcases l with e | e | e <;> rw [e] <;> decide) fun σ s h => ?_) ?_
  · obtain ⟨r, dj, fit, b⟩ := src _ σ s h
    exact ⟨r, dj.sub_right h.1.gi.kSub, fit, b⟩
  rw [hhv]
  -- `1 < h`, `h < p − 1` and both.
  refine VP.seq (ltS_vp (d := slLo) (a := aOne) (b := aH) ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64
      (Taint.ofRegs [.s6, .s9, .s10, .s11]) (sub3 aTmp aOne aH), by kernel_rfl⟩
    ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6, .s9, .s10, .s11]) (.block (stBorrow slLo)),
        by kernel_rfl⟩
    (by simp [hO]) (by simp) (by decide) (by decide)
    (by simp only [List.mem_cons, not_or]; exact ⟨by decide, by decide, hTl⟩) ⟨by decide, by decide⟩) ?_
  refine VP.seq (ltS_vp (d := slHi) (a := aH) (b := aPm1) ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64
      (Taint.ofRegs [.s6, .s9, .s10, .s11]) (sub3 aTmp aH aPm1), by kernel_rfl⟩
    ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6, .s9, .s10, .s11]) (.block (stBorrow slHi)),
        by kernel_rfl⟩
    (by simp) (by simp [hM]) (by decide) (by decide)
    (by simp only [List.mem_cons, not_or]; exact ⟨by decide, by decide, hTl⟩) ⟨by decide, by decide⟩) ?_
  refine VP.seq (andCmp_vp (d := slLo) (a := slLo) (b := slHi) ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64
      (Taint.ofRegs [.s6, .s9, .s10, .s11])
      (.block (andS slLo slLo slHi ++ ([.load .d .t2 .s11 slLo] : List Instr))), by kernel_rfl⟩
    ⟨by decide, by decide⟩ (by simp) (by simp) (by g_simp; exact ite01_le _) (by g_simp; exact ite01_le _)) ?_
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
  · -- Out of range: nothing more.
    refine VP.block_nil fun σ s ⟨⟨⟨⟨h, x⟩, _⟩, e⟩, z⟩ => ⟨?_, x⟩
    rw [e] at z
    have nr : ¬(1 < hv ∧ hv < pv - 1) := by
      intro hr; simp only [Option.some.injEq, decide_eq_true_eq] at z
      g_simp at z hOv hMv; simp only [hOv, hMv] at z
      exact z ⟨(ite01_eq_one _).mpr hr.1, (ite01_eq_one _).mpr hr.2⟩
    have nc : ¬(1 < hv ∧ hv < pv - 1 ∧ 1 < hv ^ ev % pv) := fun hc => nr ⟨hc.1, hc.2.1⟩
    simp only [gOut, nc, ↓reduceIte]
    exact h.back hkls rfl rfl rfl (kc hv)
  · by_cases hr : 1 < hv ∧ hv < pv - 1
    swap
    · refine VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => ?_
      rw [e] at z; simp only [Option.some.injEq, decide_eq_false_iff_not, Decidable.not_not] at z
      g_simp at z hOv hMv; simp only [hOv, hMv] at z
      exact hr ⟨(ite01_eq_one _).mp z.1, (ite01_eq_one _).mp z.2⟩
    have eq : gOut c G hv pv ev = if 1 < hv ^ ev % pv then
        ({ c with cl := (sG, Spec.Rsa.i2osp (hv ^ ev % pv) G.pLen) :: c.cl }).setV fG 1 else c := by
      simp only [gOut, hr, true_and]
    rw [eq]
    have eos : Spec.Rsa.os2ip hb = hv := by rw [← hhv, VG.Proof.Dsa.decodeBE_os2ip]
    generalize hgv : hv ^ ev % pv = gv
    have glt : gv < pv := hgv ▸ Nat.mod_lt _ (by omega)
    -- `g`, back at the stage `c`.
    refine VP.seq ((power_vp (c := c) (X := X) (H := H) (hb := hb) cert hPc hpv hp2
      hpo hEc hev hH hHv (fun x hx => (hcl x hx).1) (src c)).mono
      (fun σ s ⟨⟨⟨⟨h, x⟩, _⟩, _⟩, _⟩ => ⟨h.back hkls rfl rfl rfl (kc hv), x⟩)
      (G' := fun σ t => St G c X σ t ∧ Env t G.pS (pZ G.pLen) (pw G.pLen) ∧
        wordsVal t.mem G.pS (VG.Proof.Bignum.slot (pw G.pLen) 4) (pw G.pLen) = gv ∧
        (t.gpr .a0 = 0 ↔ 1 < gv ∧ gv < pv))
      fun σ t ⟨h, en, v4, r0⟩ => ⟨h, en, by rw [v4, eos, hgv], by rw [← hgv, ← eos, ← v4]; exact r0⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
      rw [eval_zero, eval_zero, beq_zero_of_iff h₁.2.2.2, beq_zero_of_iff h₂.2.2.2]) ?_ ?_
    · -- 1 < g: stored.
      by_cases h1 : 1 < gv
      · simp only [h1, ↓reduceIte]
        refine VP.assoc (VP.seq ((gStore_vp (c := c) (g := gv) fun x hx => (hcl x hx).2).mono
          (fun σ s ⟨⟨h, en, v4, _⟩, _⟩ => ⟨h, en, v4⟩) fun _ _ h => h) ?_)
        exact stImm_vp (fun σ s h => h.1) (by decide) varOk_fG fun σ s t ⟨_, x⟩ h _ => ⟨h, x⟩
      · refine VP.of_false fun σ s ⟨⟨_, _, _, r0⟩, z⟩ => h1 ?_
        rw [eval_zero, beq_zero_of_iff r0] at z
        simp only [Option.some.injEq, decide_eq_true_eq] at z
        exact z.1
    · by_cases h1 : 1 < gv
      · refine VP.of_false fun σ s ⟨⟨_, _, _, r0⟩, z⟩ => ?_
        rw [eval_zero, beq_zero_of_iff r0] at z
        simp only [Option.some.injEq, decide_eq_false_iff_not] at z
        exact z ⟨h1, glt⟩
      · simp only [h1, ↓reduceIte]
        exact VP.block_nil fun σ s ⟨⟨h, _⟩, _⟩ => h

end

end VG.Proof.Dsa.RISCV64.PSearch

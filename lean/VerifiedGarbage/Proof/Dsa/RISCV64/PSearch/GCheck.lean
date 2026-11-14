module

public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Power
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Ctl
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.PrimeCall
public import VerifiedGarbage.Proof.Dsa.Generation.RefillSeed
public import VerifiedGarbage.Proof.Dsa.Contract
import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Test
import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
import VerifiedGarbage.Proof.Dsa.Generation.GeneratorDomain
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.Generation.Chunks

-- separate module: the generator's search and the check (`gCheck_vp`), which build beside q's and p's parts (`QPart`, `PPart`), all of which the seed's attempt imports

/-! # DSA parameter search on RISC-V: the generator and the check

As on PPC64LE (`Proof/Dsa/PPC64LE/Gen/GPart.lean`, `CheckCall.lean` and
`CheckPart.lean`), over the window of the tape from the cursor `u`: its
first `generatorAttempts` candidates' octets, or fewer if the tape is
shorter (`GP.win`). `window_vp`: the window's words. `gPart_vp`: `gStep` on
each candidate of the window, until one gives a g above 1 (`fG` := 1, g at
`sG`) or the window has no candidate left (`fG` := 2), and the candidates
read counted as consumed (`fUsed`).
-/

@[expose] public section

/-! ## DSA parameter search on RISC-V: one `h` of the generator search

As on PPC64LE (`Proof/Dsa/PPC64LE/Gen/GCmp.lean` and `GStep.lean`).
`gStep` (`gStep_vp`): `h`, the `pLen` bytes at the address in `fH`, into
array `aH` of the key working space (zeroed first); unless `1 < h < p − 1`
(`ltS_vp`, `andCmp_vp`), nothing more; else `g = h^e mod p` by the power in
the P space (`power_vp`), and if `g > 1`, `g` big-endian at `sG`
(`gStore_vp`) and `fG` := 1. The `h` bytes are the caller's: the octets at
`H`, apart from `scratch` and the stack, as they were on entry (`σ`), which
every state of the search keeps.
-/

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

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64 VG.RISCV64.Steps
open VG.Impl.Dsa.RISCV64.ParameterSearch
open VG.Impl.Rsa.RISCV64.Keys (seqs)

/-! ## The window -/

namespace GP
variable (G : GP)

/-- The window's octets from `u`. -/
abbrev win (u : Nat) : Nat := min (G.randLen - u) (Spec.Dsa.generatorAttempts * G.pLen)

/-- The window's address. -/
abbrev hA (u : Nat) : Addr := G.rand + BitVec.ofNat 64 u

/-- Whether the tape held the whole window. -/
abbrev full (u : Nat) : Nat := if Spec.Dsa.generatorAttempts * G.pLen ≤ G.randLen - u then 1 else 0

/-- The window's bytes. -/
abbrev winB (u : Nat) : List Byte := (G.randB.drop u).take (Spec.Dsa.generatorAttempts * G.pLen)

end GP

theorem varOk_fH {G : GP} : VarOk G fH := varOk_of (by decide)
theorem varOk_fHLeft {G : GP} : VarOk G fHLeft := varOk_of (by decide)
theorem varOk_fHStart {G : GP} : VarOk G fHStart := varOk_of (by decide)
theorem varOk_fFull {G : GP} : VarOk G fFull := varOk_of (by decide)

theorem shl7 {x : Nat} (hx : x < 2 ^ 50) :
    BitVec.ofNat 64 x <<< 7 = BitVec.ofNat 64 (Spec.Dsa.generatorAttempts * x) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Spec.Dsa.generatorAttempts]
  rw [Nat.mod_eq_of_lt (a := x) (by omega)]
  omega

/-- The window's words, as the code stores them. -/
abbrev wCfg (c : Cfg) (G : GP) (u : Nat) : Cfg :=
  (((c.setV fH (G.hA u)).setV fHStart (G.hA u)).setV fHLeft (BitVec.ofNat 64 (G.win u))).setV fFull
    (BitVec.ofNat 64 (G.full u))

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The window from the cursor `u`: its start in `fH` and `fHStart`, its
octets in `fHLeft`, and whether the tape held it whole in `fFull`. -/
theorem window_vp {g : Geo} (hg : g.pLen = G.pLen) {u : Nat} (hu : u ≤ G.randLen) (hU : fUsed ∈ c.LS)
    (hUv : c.V fUsed = BitVec.ofNat 64 u) :
    VP (St G c X) g.window (St G (wCfg c G u) X) := by
  by_cases l : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384
  swap
  · exact VP.of_false fun σ s h => l h.1.lens
  have hp : G.pLen < 2048 := by rcases l with e | e | e <;> rw [e] <;> decide
  unfold Geo.window
  rw [hg]
  refine VP.seq (G := fun σ s => St G ((c.setV fH (G.hA u)).setV fHStart (G.hA u)) X σ s ∧
      s.gpr .t4 = BitVec.ofNat 64 (G.randLen - u) ∧
      s.gpr .t5 = BitVec.ofNat 64 (Spec.Dsa.generatorAttempts * G.pLen))
    (VP.pub (SS.pub (c := fun _ => c) fun σ s h => h.1) []
      ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6])
        (.block [ld .t2 fWit, ld .t3 fUsed, .add .t2 .t2 .t3, st .t2 fH, st .t2 fHStart, ld .t4 fWitLen,
          .sub .t4 .t4 .t3, .li .t5 G.pLen, .shift .sll .d .t5 .t5 7]), by kernel_rfl⟩
      (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ => ?_) ?_
  · have wl := h.gi.randLt
    refine h.ldK (o := fWit) (by decide) (by decide) (h.gi.fixedV (v := G.rand) (by simp [fixedWords]))
      (t := .t2) (by decide) fun s₁ h₁ u₁ => ?_
    refine h₁.ldK (o := fUsed) (by decide) (by decide) ((h₁.gi.slotV hU).trans hUv) (t := .t3) (by decide)
      fun s₂ h₂ u₂ => ?_
    refine wp_add fun s₃ u₃ => ?_
    have v3 : s₃.gpr .t2 = G.hA u := by rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr]
    have h₃ := h₂.of_upd u₃ (by decide)
    refine h₃.stF varOk_fH fun s₄ h₄ m₄ => ?_
    refine h₄.stF varOk_fHStart fun s₅ h₅ m₅ => ?_
    rw [m₄.gpr, v3] at h₅
    refine h₅.ldK (o := fWitLen) (by decide) (by decide)
      (h₅.gi.fixedV (v := BitVec.ofNat 64 G.randLen) (by simp [fixedWords])) (t := .t4) (by decide)
      fun s₆ h₆ u₆ => ?_
    refine wp_sub fun s₇ u₇ => ?_
    refine wp_li hp fun s₈ u₈ => ?_
    refine wp_sll (by decide) fun s₉ u₉ => WP.block_nil ⟨⟨?_, x⟩, ?_, ?_⟩
    · exact ((h₆.of_upd u₇ (by decide)).of_upd u₈ (by decide)).of_upd u₉ (by decide)
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₆.other _ (by decide),
        m₅.gpr, m₄.gpr, u₃.other _ (by decide), u₂.gpr, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
    · rw [u₉.gpr, u₈.gpr, shl7 (by omega)]
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [eval_ltu, eval_ltu, h₁.2.1, h₂.2.1, h₁.2.2, h₂.2.2]) ?_ ?_
  · refine VP.pub (SS.pub (c := fun _ => (c.setV fH (G.hA u)).setV fHStart (G.hA u)) fun σ s h => h.1.1.1) []
      ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block ([st .t4 fHLeft] ++ stImm fFull 0)),
        by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨⟨⟨h, x⟩, t4, t5⟩, e⟩ => ?_
    have wl := h.gi.randLt
    rw [eval_ltu, t4, t5] at e
    simp only [Option.some.injEq, decide_eq_true_eq] at e
    rw [ofNat_lt_iff (by omega) (by simp only [Spec.Dsa.generatorAttempts]; omega)] at e
    simp only [stImm, List.cons_append, List.nil_append]
    refine h.stF varOk_fHLeft fun s₁ h₁ m₁ => wp_li (by decide) fun s₂ u₂ => ?_
    refine (h₁.of_upd u₂ (by decide)).stF varOk_fFull fun s₃ h₃ m₃ => WP.block_nil ⟨?_, x⟩
    rw [u₂.gpr, t4] at h₃
    have ew : G.win u = G.randLen - u := Nat.min_eq_left (by omega)
    have ef : G.full u = 0 := by simp only [GP.full]; split <;> omega
    rw [wCfg, ew, ef]
    exact h₃
  · refine VP.pub (SS.pub (c := fun _ => (c.setV fH (G.hA u)).setV fHStart (G.hA u)) fun σ s h => h.1.1.1) []
      ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block ([st .t5 fHLeft] ++ stImm fFull 1)),
        by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨⟨⟨h, x⟩, t4, t5⟩, e⟩ => ?_
    have wl := h.gi.randLt
    rw [eval_ltu, t4, t5] at e
    simp only [Option.some.injEq, decide_eq_false_iff_not] at e
    rw [ofNat_lt_iff (by omega) (by simp only [Spec.Dsa.generatorAttempts]; omega)] at e
    simp only [stImm, List.cons_append, List.nil_append]
    refine h.stF varOk_fHLeft fun s₁ h₁ m₁ => wp_li (by decide) fun s₂ u₂ => ?_
    refine (h₁.of_upd u₂ (by decide)).stF varOk_fFull fun s₃ h₃ m₃ => WP.block_nil ⟨?_, x⟩
    rw [u₂.gpr, t5] at h₃
    have ew : G.win u = Spec.Dsa.generatorAttempts * G.pLen := Nat.min_eq_right (by omega)
    have ef : G.full u = 1 := by simp only [GP.full]; split <;> omega
    rw [wCfg, ew, ef]
    exact h₃

end

/-! ## Reordered words -/

/-- Equal header words of stages that set `fHLeft`, `fH` and `fG` over the
same words. -/
syntax "v_eq" : tactic
macro_rules
  | `(tactic| v_eq) => `(tactic| (intro o; simp only [Cfg.setV, upd, fH, fHLeft, fG, fHStart, fFull]; by_cases h1 : o = 56 <;>
      by_cases h2 : o = 48 <;> by_cases h3 : o = 104 <;> simp [h1, h2, h3]))

/-- A stage's words listed and valued as another's. -/
theorem SS.ofV {G : GP} {STK : Nat} {σ s : State} {c c' : Cfg} (h : SS G STK σ c s)
    (hLS : c'.LS ⊆ c.LS) (hV : ∀ o, c.V o = c'.V o) (hcl : ∀ x ∈ c'.cl, x ∈ c.cl)
    (hl : c'.live = c.live) (hA : c'.A = c.A) (hk : c'.kls = c.kls) (hK : c'.KV = c.KV) : SS G STK σ c' s :=
  h.mono (fun o ho => ⟨hLS ho, hV o⟩) hcl (fun j hj => ⟨hl ▸ hj, by rw [hA]⟩)
    (fun d hd => ⟨hk ▸ hd, by rw [hK]⟩)

/-- Simplifies inclusions of the header words listed. -/
syntax "ls_sub" : tactic
macro_rules
  | `(tactic| ls_sub) => `(tactic|
      (simp only [Cfg.setV, List.cons_subset, List.mem_cons, true_or, or_true, true_and]; intro o ho; simp [ho]))

/-! ## The candidates -/

namespace GP
variable (G : GP)

/-- The candidates the window holds. -/
abbrev nW (u : Nat) : Nat := G.win u / G.pLen

/-- The candidate at byte `i` of the window. -/
abbrev hAt (u i : Nat) : List Byte := ((G.winB u).drop i).take G.pLen

/-- The candidates from the `k`-th on. -/
abbrev gList (u k : Nat) : List Nat :=
  (Spec.Dsa.generationChunks G.pLen ((G.winB u).drop (k * G.pLen))).map Spec.Dsa.decodeBE

end GP

/-- Whether the candidate at byte `i` of the window gives a g above 1. -/
abbrev gOk (G : GP) (u pv ev i : Nat) : Prop :=
  1 < Spec.Dsa.decodeBE (G.hAt u i) ∧ Spec.Dsa.decodeBE (G.hAt u i) < pv - 1 ∧
    1 < Spec.Dsa.decodeBE (G.hAt u i) ^ ev % pv

/-- The search's iterations from the `k`-th candidate, with `m` left. -/
def gCount (G : GP) (u pv ev : Nat) : Nat → Nat → Nat
  | 0, k => k + 1
  | m + 1, k => if gOk G u pv ev (k * G.pLen) then k + 1 else gCount G u pv ev m (k + 1)

theorem gCount_gt (G : GP) (u pv ev : Nat) : ∀ m k, k < gCount G u pv ev m k
  | 0, k => by simp [gCount]
  | m + 1, k => by
    simp only [gCount]; split
    · omega
    · exact Nat.lt_of_succ_lt (gCount_gt G u pv ev m (k + 1))

/-- The search's words at the `k`-th candidate. -/
abbrev gCfg (c : Cfg) (G : GP) (u k : Nat) : Cfg :=
  (((wCfg c G u).setV fH (G.hA u + BitVec.ofNat 64 (k * G.pLen))).setV fHLeft
    (BitVec.ofNat 64 (G.win u - k * G.pLen))).setV fG 4

/-- The stage after the search, from its result and the candidates read. -/
def gFin (c : Cfg) (G : GP) (u : Nat) : Option Nat → Nat → Cfg
  | some g, n => ((({ wCfg c G u with cl := (sG, Spec.Rsa.i2osp g G.pLen) :: c.cl }).setV fH
      (G.hA u + BitVec.ofNat 64 (n * G.pLen))).setV fHLeft (BitVec.ofNat 64 (G.win u - n * G.pLen))).setV fG 1
  | none, n => (((wCfg c G u).setV fH (G.hA u + BitVec.ofNat 64 (n * G.pLen))).setV fHLeft
      (BitVec.ofNat 64 (G.win u - n * G.pLen))).setV fG 2

/-- The search with `r` iterations left of `N`. -/
abbrev gInv (c : Cfg) (G : GP) (u pv ev qv N : Nat) (X : State → Prop) (r : Nat) (σ s : State) : Prop :=
  (r ≤ N ∧ N - r ≤ G.nW u ∧ gCount G u pv ev (G.nW u - (N - r)) (N - r) = N ∧
    Spec.Dsa.generator pv qv (G.gList u (N - r)) = Spec.Dsa.generator pv qv (G.gList u 0) ∧
    Proof.Dsa.Generation.generatorCount pv qv (G.gList u 0) =
      (N - r) + Proof.Dsa.Generation.generatorCount pv qv (G.gList u (N - r))) ∧
  St G (gCfg c G u (N - r)) X σ s

/-- What `gStep` needs of the stage the search starts from. -/
structure GReq (G : GP) (c : Cfg) (pv ev : Nat) : Prop where
  hM : aPm1 ∈ c.live
  hMv : c.A aPm1 = pv - 1
  hO : aOne ∈ c.live
  hOv : c.A aOne = 1
  hZ : aZero ∈ c.live
  hZv : c.A aZero = 0
  hHl : aH ∉ c.live
  hTl : aTmp ∉ c.live
  hkls : c.kls = []
  hPc : (sPBE, Spec.Rsa.i2osp pv G.pLen) ∈ c.cl
  hpv : pv < 256 ^ G.pLen
  hp2 : 2 ≤ pv
  hpo : pv % 2 = 1
  hEc : (sE, Spec.Rsa.i2osp ev (eBytes G.pLen G.qLen)) ∈ c.cl
  hev : ev < 256 ^ eBytes G.pLen G.qLen
  hcl : ∀ x ∈ c.cl, Apart pB (pZ G.pLen) x ∧ Apart sG G.pLen x
  hfH : fH ∉ c.LS
  hfL : fHLeft ∉ c.LS

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- Bytes of the tape, in the entry's memory. -/
theorem rand_slice {σ : State} (hG : mkG σ = G) {j n : Nat} (hj : j + n ≤ G.randLen) :
    Spec.Rsa.bytesAt σ.mem (G.rand + BitVec.ofNat 64 j) n = (G.randB.drop j).take n := by
  have hw : G.randB = Spec.Rsa.bytesAt σ.mem G.rand G.randLen := by rw [← hG]; rfl
  obtain ⟨d, hd⟩ : ∃ d, G.randLen = j + (n + d) := ⟨G.randLen - j - n, by omega⟩
  rw [hw, hd, VG.Proof.Dsa.Generation.bytesAt_append, VG.Proof.Dsa.Generation.bytesAt_append,
    List.drop_left' (by simp [Spec.Rsa.bytesAt]), List.take_left' (by simp [Spec.Rsa.bytesAt])]

/-- The `k`-th candidate, read from the entry's memory: what `gStep` needs. -/
theorem cand_src {σ : State} (hσ : CIn STK0 σ) (hG : mkG σ = G) {u k : Nat} (hp0 : 0 < G.pLen)
    (hk : u + (k + 1) * G.pLen ≤ G.randLen) (hkw : (k + 1) * G.pLen ≤ Spec.Dsa.generatorAttempts * G.pLen) :
    (∀ i < G.pLen, InRegions (σ.rd ++ σ.wr) (VG.Proof.Bignum.off (G.hA u + BitVec.ofNat 64 (k * G.pLen)) i) 1) ∧
      Region.Disjoint ⟨G.hA u + BitVec.ofNat 64 (k * G.pLen), G.pLen⟩ G.rScr ∧
      Region.Disjoint ⟨G.hA u + BitVec.ofNat 64 (k * G.pLen), G.pLen⟩ (rBelow σ STK0) ∧
      (G.hA u + BitVec.ofNat 64 (k * G.pLen)).toNat + G.pLen ≤ 2 ^ 64 ∧
      Spec.Rsa.bytesAt σ.mem (G.hA u + BitVec.ofNat 64 (k * G.pLen)) G.pLen = G.hAt u (k * G.pLen) := by
  have fit : G.rand.toNat + G.randLen ≤ 2 ^ 64 := by have := hσ.nR; rw [← hG]; exact this
  have rl : G.randLen < 2 ^ 64 := by rw [← hG]; exact (σ.gpr .a4).isLt
  have eA : G.hA u + BitVec.ofNat 64 (k * G.pLen) = G.rand + BitVec.ofNat 64 (u + k * G.pLen) := by
    rw [GP.hA, BitVec.add_assoc, BitVec.ofNat_add]
  have e1 : (k + 1) * G.pLen = k * G.pLen + G.pLen := Nat.succ_mul _ _
  rw [eA]
  have sub : Region.Sub ⟨G.rand + BitVec.ofNat 64 (u + k * G.pLen), G.pLen⟩ G.rRand :=
    Offset.sub_base _ (by omega)
  have rC := hσ.rC; rw [hG] at rC
  have bR := hσ.bR; rw [hG] at bR
  refine ⟨fun i hi => ⟨G.rRand, ?_, ?_⟩, rC.sub_left sub, bR.symm.sub_left sub, ?_, ?_⟩
  · rw [hσ.rd, hG]; simp
  · rw [VG.Proof.Bignum.off, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base _ (by omega) (by omega)
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := u + k * G.pLen) (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [rand_slice hG (by omega), GP.hAt, GP.winB, List.drop_take, List.drop_drop, List.take_take]
    congr 1
    omega

/-- The next candidate: `fH` := `fH` + `pLen`, `fHLeft` := `fHLeft` − `pLen`. -/
theorem adv_vp {d : Cfg} (hH : fH ∈ d.LS) (hL : fHLeft ∈ d.LS) (hp : G.pLen < 2048) :
    VP (St G d X) (.block [ld .t2 fH, .addi .t2 .t2 G.pLen, st .t2 fH, ld .t2 fHLeft,
        .addi .t2 .t2 (-(G.pLen : Int)), st .t2 fHLeft])
      (St G ((d.setV fH (d.V fH + BitVec.ofNat 64 G.pLen)).setV fHLeft (d.V fHLeft - BitVec.ofNat 64 G.pLen)) X) := by
  refine VP.pub (SS.pub (c := fun _ => d) fun σ s h => h.1) []
    ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block [ld .t2 fH, .addi .t2 .t2 G.pLen,
      st .t2 fH, ld .t2 fHLeft, .addi .t2 .t2 (-(G.pLen : Int)), st .t2 fHLeft]), by kernel_rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ => ?_
  refine h.ldK (o := fH) (by decide) (by decide) (h.gi.slotV hH) (t := .t2) (by decide) fun s₁ h₁ u₁ => ?_
  refine wp_addi hp fun s₂ u₂ => ?_
  refine (h₁.of_upd u₂ (by decide)).stF varOk_fH fun s₃ h₃ m₃ => ?_
  rw [u₂.gpr, u₁.gpr] at h₃
  refine h₃.ldK (o := fHLeft) (v := d.V fHLeft) (by decide) (by decide)
    ((h₃.gi.slotV (List.mem_cons_of_mem _ hL)).trans (by simp [upd, fH, fHLeft])) (t := .t2) (by decide)
    fun s₄ h₄ u₄ => ?_
  refine wp_subi (by omega) fun s₅ u₅ => ?_
  refine (h₄.of_upd u₅ (by decide)).stF varOk_fHLeft fun s₆ h₆ _ => WP.block_nil ⟨?_, x⟩
  rw [u₅.gpr, u₄.gpr] at h₆
  exact h₆

end

/-! ## The search for g -/

/-- A piece from a stage with a fact both runs share. -/
theorem VP.ofPure {P : Prop} {F Q : State → State → Prop} {c : Prog isa} (h : P → VP F c Q) :
    VP (fun σ s => P ∧ F σ s) c Q := by
  by_cases hp : P
  · exact (h hp).mono (fun σ s h => h.2) fun _ _ h => h
  · exact VP.of_false fun σ s h => hp h.1

/-- The stage's call, with the facts of its entry the candidates' reads need. -/
abbrev XE (G : GP) (X : State → Prop) (σ : State) : Prop := X σ ∧ CIn STK0 σ ∧ mkG σ = G

section
variable {G : GP} {c : Cfg} {X : State → Prop}

theorem winB_length {u : Nat} (hRL : G.randB.length = G.randLen) : (G.winB u).length = G.win u := by
  simp only [GP.winB, GP.win, List.length_take, List.length_drop, hRL]
  exact Nat.min_comm _ _

theorem gBody_vp {g : Geo} (hg : g.pLen = G.pLen) (hgq : g.qLen = G.qLen) (cert : CertC G.pLen G.qLen)
    {u pv ev qv N : Nat} (R : GReq G c pv ev) (hu : u ≤ G.randLen) (hRL : G.randB.length = G.randLen)
    (hev' : ev = (pv - 1) / qv) (r : Nat) :
    VP (gInv c G u pv ev qv N X (r + 1)) (seqs [.block [ld .t2 fHLeft, .li .t3 g.pLen],
        .ite (.ltu .t2 .t3) (.block (stImm fG 2))
          (seqs [g.gStep, .block [ld .t2 fH, .addi .t2 .t2 g.pLen, st .t2 fH, ld .t2 fHLeft,
            .addi .t2 .t2 (-(g.pLen : Int)), st .t2 fHLeft]]),
        .block (cmpF fG 4)])
      (fun σ s => isa.eval (.zero .t2) s = some (decide (0 < r)) ∧
        (r = 0 → St G (gFin c G u (Spec.Dsa.generator pv qv (G.gList u 0))
          (Proof.Dsa.Generation.generatorCount pv qv (G.gList u 0))) X σ s) ∧
        (0 < r → gInv c G u pv ev qv N X r σ s)) := by
  refine VP.ofPure fun ⟨hr, hk, hc, hres, hcnt⟩ => ?_
  by_cases l : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384
  swap
  · exact VP.of_false fun σ s h => l h.1.lens
  have hp : G.pLen < 2048 := by rcases l with e | e | e <;> rw [e] <;> decide
  have hpL : 0 < G.pLen := by rcases l with e | e | e <;> rw [e] <;> decide
  have hfL := R.hfL
  have hfH := R.hfH
  have hWl := winB_length (u := u) hRL
  generalize hMM : G.nW u = M at hk hc
  generalize hkk : N - (r + 1) = k at hk hc hres hcnt ⊢
  have kL : ∀ j, j ≤ M → j * G.pLen ≤ G.win u := fun j hj =>
    Nat.le_trans (Nat.mul_le_mul_right _ hj) (hMM ▸ Nat.div_mul_le_self _ _)
  have hWr : G.win u ≤ Spec.Dsa.generatorAttempts * G.pLen := Nat.min_le_right _ _
  have hW64 : G.win u < 2 ^ 64 := by simp only [Spec.Dsa.generatorAttempts] at hWr; omega
  have hWu : G.win u + u ≤ G.randLen := by
    have := Nat.min_le_left (G.randLen - u) (Spec.Dsa.generatorAttempts * G.pLen); simp only [GP.win]; omega
  rw [hg]
  -- Whether a candidate is left.
  refine VP.seq (G := fun σ s => St G (gCfg c G u k) X σ s ∧
      s.gpr .t2 = BitVec.ofNat 64 (G.win u - k * G.pLen) ∧ s.gpr .t3 = BitVec.ofNat 64 G.pLen)
    (VP.pub (SS.pub (c := fun _ => gCfg c G u k) fun σ s h => h.1) []
      ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block [ld .t2 fHLeft, .li .t3 G.pLen]),
        by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ =>
      h.ldK (o := fHLeft) (v := BitVec.ofNat 64 (G.win u - k * G.pLen)) (by decide) (by decide)
        ((h.gi.slotV (by simp)).trans (by simp [upd, fHLeft, fG])) (t := .t2) (by decide)
        fun s₁ h₁ u₁ => wp_li hp fun s₂ u₂ => WP.block_nil
          ⟨⟨h₁.of_upd u₂ (by decide), x⟩, by rw [u₂.other _ (by decide), u₁.gpr], u₂.gpr⟩) ?_
  have hcnd : ∀ σ₁ σ₂ s₁ s₂, (fun σ s => St G (gCfg c G u k) X σ s ∧
      s.gpr .t2 = BitVec.ofNat 64 (G.win u - k * G.pLen) ∧ s.gpr .t3 = BitVec.ofNat 64 G.pLen) σ₁ s₁ →
      (fun σ s => St G (gCfg c G u k) X σ s ∧
      s.gpr .t2 = BitVec.ofNat 64 (G.win u - k * G.pLen) ∧ s.gpr .t3 = BitVec.ofNat 64 G.pLen) σ₂ s₂ →
      isa.eval (.ltu .t2 .t3) s₁ = isa.eval (.ltu .t2 .t3) s₂ :=
    fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [eval_ltu, eval_ltu, h₁.2.1, h₂.2.1, h₁.2.2, h₂.2.2]
  have evc : ∀ s : State, s.gpr .t2 = BitVec.ofNat 64 (G.win u - k * G.pLen) →
      s.gpr .t3 = BitVec.ofNat 64 G.pLen →
      isa.eval (.ltu .t2 .t3) s = some (decide (G.win u - k * G.pLen < G.pLen)) := fun s a b => by
    rw [eval_ltu, a, b]
    simp only [Option.some.injEq]
    exact decide_eq_decide.mpr (ofNat_lt_iff (by omega) (by omega))
  rcases Nat.lt_or_ge k M with hkM | hkM
  · -- A candidate: `gStep`, then the next.
    have hi : (k + 1) * G.pLen ≤ G.win u := kL (k + 1) hkM
    have hi' : k * G.pLen + G.pLen ≤ G.win u := by rw [Nat.succ_mul] at hi; exact hi
    have notLeft : ∀ σ s, ¬((St G (gCfg c G u k) X σ s ∧
        s.gpr .t2 = BitVec.ofNat 64 (G.win u - k * G.pLen) ∧ s.gpr .t3 = BitVec.ofNat 64 G.pLen) ∧
        isa.eval (.ltu .t2 .t3) s = some true) := fun σ s ⟨⟨_, a, b⟩, z⟩ => by
      rw [evc s a b] at z; simp only [Option.some.injEq, decide_eq_true_eq] at z; omega
    obtain ⟨m, hm⟩ : ∃ m, M - k = m + 1 := ⟨M - k - 1, by omega⟩
    rw [hm] at hc; simp only [gCount] at hc
    have hlen : G.pLen ≤ ((G.winB u).drop (k * G.pLen)).length := by
      rw [List.length_drop, hWl]; omega
    have hstep := VG.Proof.Dsa.Generation.generator_chunks_step (p := pv) (q := qv) hpL hlen
    have hcs := VG.Proof.Dsa.Generation.generatorCount_chunks_step (p := pv) (q := qv) hpL hlen
    simp only [VG.Proof.Dsa.powMod_eq, ← hev', List.drop_drop] at hstep hcs
    have eD : k * G.pLen + G.pLen = (k + 1) * G.pLen := (Nat.succ_mul _ _).symm
    rw [eD] at hstep hcs
    have stepVP := gStep_vp (c := gCfg c G u k) (X := XE G X) (H := G.hA u + BitVec.ofNat 64 (k * G.pLen))
      (hb := G.hAt u (k * G.pLen)) hg hgq cert R.hM R.hMv R.hO R.hOv R.hZ R.hZv R.hHl R.hTl R.hkls R.hPc R.hpv
      R.hp2 R.hpo R.hEc R.hev R.hcl (by simp) (by simp [upd, fH, fHLeft, fG])
      (fun σ ⟨_, hσ, hG⟩ => cand_src hσ hG hpL (by omega) (by omega))
    by_cases hok : gOk G u pv ev (k * G.pLen)
    · -- It gives g: done.
      have r0 : r = 0 := by rw [ite_eq_left_of_eq_true _ _ (eq_true hok)] at hc; omega
      subst r0
      have some0 : Spec.Dsa.generator pv qv (G.gList u 0) =
          some (Spec.Dsa.decodeBE (G.hAt u (k * G.pLen)) ^ ev % pv) := by
        rw [← hres, GP.gList, hstep]; exact ite_eq_left_of_eq_true _ _ (eq_true hok)
      have cnt0 : Proof.Dsa.Generation.generatorCount pv qv (G.gList u 0) = k + 1 := by
        rw [hcnt, GP.gList, hcs, ite_eq_left_of_eq_true _ _ (eq_true hok)]
      have hG1 : gOut (gCfg c G u k) G (Spec.Dsa.decodeBE (G.hAt u (k * G.pLen))) pv ev =
          ({ gCfg c G u k with cl := (sG, Spec.Rsa.i2osp (Spec.Dsa.decodeBE (G.hAt u (k * G.pLen)) ^ ev % pv)
            G.pLen) :: (gCfg c G u k).cl }).setV fG 1 := by
        rw [gOut, ite_eq_left_of_eq_true _ _ (eq_true hok)]
      rw [hG1] at stepVP
      refine VP.seq (VP.ite hcnd (VP.of_false notLeft)
        (VP.seq (stepVP.mono (fun σ s h => ⟨h.1.1.1, h.1.1.2, h.1.1.1.gi.pre, h.1.1.1.gi.hG⟩)
          fun σ s h => ⟨h.1, h.2.1⟩) (adv_vp (by simp) (by simp) hp))) ?_
      refine cmpF_vp (x := BitVec.ofNat 64 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd, fH, fHLeft, fG]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨by rw [e]; rfl, fun _ => ⟨?_, x⟩, fun h0 => absurd h0 (by decide)⟩
      rw [some0, cnt0]
      have eH : G.hA u + BitVec.ofNat 64 (k * G.pLen) + BitVec.ofNat 64 G.pLen =
          G.hA u + BitVec.ofNat 64 ((k + 1) * G.pLen) := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, eD]
      have eL : BitVec.ofNat 64 (G.win u - k * G.pLen) - BitVec.ofNat 64 G.pLen =
          BitVec.ofNat 64 (G.win u - (k + 1) * G.pLen) := by
        rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega), ← eD, Nat.sub_add_eq]
      have e1 : ((({ gCfg c G u k with cl := (sG, Spec.Rsa.i2osp (Spec.Dsa.decodeBE (G.hAt u (k * G.pLen)) ^ ev % pv)
            G.pLen) :: (gCfg c G u k).cl }).setV fG 1).V fH) = G.hA u + BitVec.ofNat 64 (k * G.pLen) := by
        simp [upd, fH, fHLeft, fG]
      have e2 : ((({ gCfg c G u k with cl := (sG, Spec.Rsa.i2osp (Spec.Dsa.decodeBE (G.hAt u (k * G.pLen)) ^ ev % pv)
            G.pLen) :: (gCfg c G u k).cl }).setV fG 1).V fHLeft) = BitVec.ofNat 64 (G.win u - k * G.pLen) := by
        simp [upd, fHLeft, fG]
      rw [e1, e2, eH, eL] at h'
      refine h'.ofV (by simp only [gFin]; ls_sub) (by simp only [gFin]; v_eq) (fun y hy => hy) rfl rfl rfl rfl
    · -- It does not: the next candidate.
      rw [ite_eq_right_of_eq_false _ _ (eq_false hok)] at hc
      have rpos : 0 < r := by have := gCount_gt G u pv ev m (k + 1); omega
      have hNr : N - r = k + 1 := by omega
      have hG1 : gOut (gCfg c G u k) G (Spec.Dsa.decodeBE (G.hAt u (k * G.pLen))) pv ev = gCfg c G u k := by
        rw [gOut, ite_eq_right_of_eq_false _ _ (eq_false hok)]
      rw [hG1] at stepVP
      refine VP.seq (VP.ite hcnd (VP.of_false notLeft)
        (VP.seq (stepVP.mono (fun σ s h => ⟨h.1.1.1, h.1.1.2, h.1.1.1.gi.pre, h.1.1.1.gi.hG⟩)
          fun σ s h => ⟨h.1, h.2.1⟩) (adv_vp (by simp) (by simp) hp))) ?_
      have eH : G.hA u + BitVec.ofNat 64 (k * G.pLen) + BitVec.ofNat 64 G.pLen =
          G.hA u + BitVec.ofNat 64 ((k + 1) * G.pLen) := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, eD]
      have eL : BitVec.ofNat 64 (G.win u - k * G.pLen) - BitVec.ofNat 64 G.pLen =
          BitVec.ofNat 64 (G.win u - (k + 1) * G.pLen) := by
        rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega), ← eD, Nat.sub_add_eq]
      have e1 : (gCfg c G u k).V fH = G.hA u + BitVec.ofNat 64 (k * G.pLen) := by simp [upd, fH, fHLeft, fG]
      have e2 : (gCfg c G u k).V fHLeft = BitVec.ofNat 64 (G.win u - k * G.pLen) := by
        simp [upd, fHLeft, fG]
      refine cmpF_vp (x := BitVec.ofNat 64 4) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd, fH, fHLeft, fG]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨by rw [e]; simp [rpos], fun h0 => absurd h0 (by omega), fun _ => ?_⟩
      simp only [gInv, hNr]
      refine ⟨⟨by omega, by omega, by rw [hMM, show M - (k + 1) = m by omega]; exact hc, ?_, ?_⟩, ?_, x⟩
      · rw [← hres, GP.gList, GP.gList, hstep, ite_eq_right_of_eq_false _ _ (eq_false hok)]
      · rw [hcnt, GP.gList, GP.gList, hcs, ite_eq_right_of_eq_false _ _ (eq_false hok)]; omega
      · rw [e1, e2, eH, eL] at h'
        exact h'.ofV (by ls_sub) (by v_eq) (fun y hy => hy) rfl rfl rfl rfl
  · -- The window is done: `fG` := 2.
    have hkM' : k = M := by omega
    subst hkM'
    have r0 : r = 0 := by simp only [Nat.sub_self, gCount] at hc; omega
    subst r0
    have hz : G.win u - k * G.pLen < G.pLen := by
      have h1 := Nat.lt_mul_div_succ (G.win u) hpL
      rw [show G.win u / G.pLen = k from hMM, Nat.mul_succ, Nat.mul_comm] at h1
      omega
    have hdone : ((G.winB u).drop (k * G.pLen)).length < G.pLen := by rw [List.length_drop, hWl]; exact hz
    have none0 : Spec.Dsa.generator pv qv (G.gList u 0) = none := by
      rw [← hres, GP.gList, VG.Proof.Dsa.Generation.generationChunks_done hdone]; rfl
    have cnt0 : Proof.Dsa.Generation.generatorCount pv qv (G.gList u 0) = k := by
      rw [hcnt, GP.gList, VG.Proof.Dsa.Generation.generatorCount_chunks_done hdone, Nat.add_zero]
    refine VP.seq (G := St G ((gCfg c G u k).setV fG (BitVec.ofNat 64 2)) X) (VP.ite hcnd
      (stImm_vp (c := fun _ => gCfg c G u k) (o := fG) (v := 2) (fun σ s h => h.1.1.1) (by decide)
        varOk_fG fun σ s t h h' _ => ⟨h', h.1.1.2⟩)
      (VP.of_false fun σ s ⟨⟨_, a, b⟩, z⟩ => by
        rw [evc s a b] at z; simp only [Option.some.injEq, decide_eq_false_iff_not] at z; omega)) ?_
    refine cmpF_vp (c := fun _ => (gCfg c G u k).setV fG (BitVec.ofNat 64 2)) (x := BitVec.ofNat 64 2)
      (fun σ s h => h.1) (by decide) (by decide) (by decide) (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd]))
      fun σ s t ⟨_, x⟩ h' _ e => ⟨by rw [e]; rfl, fun _ => ⟨?_, x⟩, fun h0 => absurd h0 (by decide)⟩
    rw [none0, cnt0]
    exact h'.ofV (by simp only [gFin]; ls_sub) (by simp only [gFin]; v_eq) (fun y hy => hy) rfl rfl rfl rfl

end

/-- The candidates the search reads. -/
abbrev nRead (G : GP) (u pv qv : Nat) : Nat := Proof.Dsa.Generation.generatorCount pv qv (G.gList u 0)

/-- After the search for g: its result, and `fUsed` past the candidates read. -/
abbrev gpCfg (c : Cfg) (G : GP) (u pv qv : Nat) : Cfg :=
  (gFin c G u (Spec.Dsa.generator pv qv (G.gList u 0)) (nRead G u pv qv)).setV fUsed
    (BitVec.ofNat 64 (u + G.pLen * nRead G u pv qv))

section
variable {G : GP} {c : Cfg} {X : State → Prop}

theorem gFin_words {u : Nat} (res : Option Nat) (n : Nat) (hU : fUsed ∈ c.LS) :
    fH ∈ (gFin c G u res n).LS ∧ (gFin c G u res n).V fH = G.hA u + BitVec.ofNat 64 (n * G.pLen) ∧
      fHStart ∈ (gFin c G u res n).LS ∧ (gFin c G u res n).V fHStart = G.hA u ∧
      fUsed ∈ (gFin c G u res n).LS ∧ (gFin c G u res n).V fUsed = c.V fUsed := by
  have hU' : (24 : Nat) ∈ c.LS := hU
  cases res <;> simp [gFin, upd, fH, fHStart, fUsed, fHLeft, fG, fFull, hU']

/-- The candidates read, counted as consumed: `fUsed` += `fH` − `fHStart`. -/
theorem used_vp {u : Nat} {res : Option Nat} {n : Nat} (hU : fUsed ∈ c.LS) (hUv : c.V fUsed = BitVec.ofNat 64 u) :
    VP (St G (gFin c G u res n) X)
      (.block [ld .t2 fH, ld .t3 fHStart, .sub .t2 .t2 .t3, ld .t3 fUsed, .add .t3 .t3 .t2, st .t3 fUsed])
      (St G ((gFin c G u res n).setV fUsed (BitVec.ofNat 64 (u + G.pLen * n))) X) := by
  obtain ⟨m1, v1, m2, v2, m3, v3⟩ := gFin_words (G := G) (u := u) res n hU
  refine VP.pub (SS.pub (c := fun _ => gFin c G u res n) fun σ s h => h.1) []
    ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6])
      (.block [ld .t2 fH, ld .t3 fHStart, .sub .t2 .t2 .t3, ld .t3 fUsed, .add .t3 .t3 .t2, st .t3 fUsed]),
      by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ => ?_
  refine h.ldK (o := fH) (by decide) (by decide) ((h.gi.slotV m1).trans v1) (t := .t2) (by decide)
    fun s₁ h₁ u₁ => ?_
  refine h₁.ldK (o := fHStart) (by decide) (by decide) ((h₁.gi.slotV m2).trans v2) (t := .t3) (by decide)
    fun s₂ h₂ u₂ => ?_
  refine wp_sub fun s₃ u₃ => ?_
  have h₃ := h₂.of_upd u₃ (by decide)
  refine h₃.ldK (o := fUsed) (by decide) (by decide) ((h₃.gi.slotV m3).trans (v3.trans hUv)) (t := .t3)
    (by decide) fun s₄ h₄ u₄ => ?_
  refine wp_add fun s₅ u₅ => ?_
  refine (h₄.of_upd u₅ (by decide)).stF varOk_fUsed fun t ht _ => WP.block_nil ⟨?_, x⟩
  have e : s₅.gpr .t3 = BitVec.ofNat 64 (u + G.pLen * n) := by
    rw [u₅.gpr, u₄.gpr, u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr,
      BitVec.add_comm (G.hA u), BitVec.add_sub_cancel, ← BitVec.ofNat_add, Nat.mul_comm]
  rw [e] at ht
  exact ht

/-- The search for g over the window from the cursor `u`: its result and the
candidates it read, which `fUsed` counts as consumed. -/
theorem gPart_vp {g : Geo} (hg : g.pLen = G.pLen) (hgq : g.qLen = G.qLen) (cert : CertC G.pLen G.qLen)
    {u pv ev qv : Nat} (R : GReq G c pv ev) (hu : u ≤ G.randLen) (hRL : G.randB.length = G.randLen)
    (hev' : ev = (pv - 1) / qv) (hU : fUsed ∈ c.LS) (hUv : c.V fUsed = BitVec.ofNat 64 u) :
    VP (St G c X) g.gPart (St G (gpCfg c G u pv qv) X) := by
  unfold Geo.gPart
  refine VP.seq (window_vp hg hu hU hUv) ?_
  have hN := gCount_gt G u pv ev (G.nW u) 0
  generalize hNN : gCount G u pv ev (G.nW u) 0 = N at hN
  refine VP.seq (G := gInv c G u pv ev qv N X N)
    (stImm_vp (c := fun _ => wCfg c G u) (o := fG) (v := 4) (fun σ s h => h.1) (by decide) varOk_fG
      fun σ s t h h' _ => ⟨⟨Nat.le_refl _, by simp, by simp only [Nat.sub_self, Nat.sub_zero]; exact hNN,
        by rw [Nat.sub_self], by simp⟩, ?_, h.2⟩) ?_
  · rw [Nat.sub_self]
    exact h'.ofV (by ls_sub) (by v_eq) (fun y hy => hy) rfl rfl rfl rfl
  rw [show N = N - 1 + 1 by omega]
  exact VP.seq (VP.loop (I := gInv c G u pv ev qv (N - 1 + 1) X) (gBody_vp hg hgq cert R hu hRL hev') _)
    (used_vp hU hUv)

end

/-! ## The check's call -/

/-- A verified domain check, with the stack it uses. -/
structure CheckOk (code : Prog isa) : Prop where
  verified : Verified target code (Proof.Dsa.checkParametersContract abi)
  stack : sdepth code ≤ STK0

/-- The check's contract. -/
abbrev checkK : Contract isa := Proof.Dsa.checkParametersContract abi

/-- The precondition, as facts. -/
structure CkIn (s : State) : Prop where
  sp16 : s.sp.toNat % 16 = 0
  rd : s.rd = [⟨s.gpr .a0, (s.gpr .a1).toNat⟩]
  wr : s.wr = [⟨s.gpr .a4, (s.gpr .a5).toNat * 8⟩]
  rW : Region.Disjoint ⟨s.gpr .a0, (s.gpr .a1).toNat⟩ ⟨s.gpr .a4, (s.gpr .a5).toNat * 8⟩
  fr : (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64
  fw : (s.gpr .a4).toNat + (s.gpr .a5).toNat * 8 ≤ 2 ^ 64
  lens : Spec.Dsa.lengthsValid (s.gpr .a2).toNat (s.gpr .a3).toNat
  len : (s.gpr .a1).toNat = 2 * (s.gpr .a2).toNat + (s.gpr .a3).toNat
  words : Spec.Dsa.scratchWords (s.gpr .a2).toNat ≤ (s.gpr .a5).toNat
  al : (s.gpr .a4).toNat % 8 = 0

theorem pre_of_ckin {s : State} (h : CkIn s) : checkK.pre s := by
  sig_pre [checkK, Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs]
  exact ⟨h.sp16, h.rd, h.wr, h.rW, h.fr, h.fw, h.lens, h.len, h.words, h.al⟩

/-- The verdict on the parameters at `a0`. -/
abbrev ckRes (s : State) : Bool :=
  Spec.Dsa.checkParametersBytes (s.gpr .a2).toNat (s.gpr .a3).toNat
    (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat)

theorem cpost_of_post {s t : State} (h : checkK.post s t) :
    ((t.gpr .a0).setWidth 32).toNat = if ckRes s = true then 1 else 0 := by
  sig_post [checkK, Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs] at h
  exact h

/-- Two calls with the same arguments and parameters. -/
theorem cpub_of {s t : State} (sp : s.sp = t.sp) (p0 : s.gpr .a0 = t.gpr .a0) (p1 : s.gpr .a1 = t.gpr .a1)
    (p2 : s.gpr .a2 = t.gpr .a2) (p3 : s.gpr .a3 = t.gpr .a3) (p4 : s.gpr .a4 = t.gpr .a4)
    (p5 : s.gpr .a5 = t.gpr .a5)
    (hb : Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat = Spec.Rsa.bytesAt t.mem (t.gpr .a0) (t.gpr .a1).toNat) :
    checkK.pub s t := by
  sig_pub [checkK, Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs]
  exact ⟨sp, by rw [hb], p0, p1, p2, p3, p4, p5⟩

/-- The bytes of p‖q‖g. -/
abbrev nPk (G : GP) : Nat := 2 * G.pLen + G.qLen

/-- The check's arguments, in `a0`–`a5`. -/
abbrev CArgs (G : GP) (s : State) : Prop :=
  s.gpr .a0 = G.sa sPacked ∧ s.gpr .a1 = BitVec.ofNat 64 (nPk G) ∧ s.gpr .a2 = BitVec.ofNat 64 G.pLen ∧
    s.gpr .a3 = BitVec.ofNat 64 G.qLen ∧ s.gpr .a4 = G.sa (wB G.pLen) ∧ s.gpr .a5 = BitVec.ofNat 64 G.wsW

/-- The regions the check is given. -/
abbrev cRd (G : GP) : List Region := [⟨G.sa sPacked, (BitVec.ofNat 64 (nPk G)).toNat⟩]
abbrev cWr (G : GP) : List Region := [⟨G.sa (wB G.pLen), (BitVec.ofNat 64 G.wsW).toNat * 8⟩]

/-- The check's entry. -/
abbrev cEntry (G : GP) (s : State) : State := s.callEntry.withRegions (cRd G) (cWr G)

section
variable {G : GP} {σ s : State} {c : Cfg}

theorem cEntry_gpr {r : Reg} (hr : r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5]) : (cEntry G s).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]

/-- The sizes of the check's arguments. -/
theorem ck_sizes (hl : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384) :
    sPacked + nPk G ≤ wB G.pLen ∧ Spec.Dsa.lengthsValid G.pLen G.qLen ∧ hEnd ≤ sPacked ∧ nPk G < 2048 ∧
      G.pLen < 2048 ∧ G.qLen < 2048 ∧ 0 < G.qLen ∧ wB G.pLen / 4096 < 8 ∧ wB G.pLen % 4096 = 0 := by
  rcases hl with e | e | e <;> simp only [nPk, GP.qLen, Spec.Dsa.generationQLen, e] <;> decide

/-- The check's arguments meet its precondition. -/
theorem SS.cEntry_ckin (h : SS G STK0 σ c s) (regs : CArgs G s) : CkIn (cEntry G s) := by
  have gi := h.gi
  have fit := gi.scrFit
  obtain ⟨w63, wEq, wPos, w8⟩ := h.wsFit
  obtain ⟨hsz, lv, hE, n11, p11, q11, q0, _⟩ := ck_sizes gi.lens
  have hp0 : 0 < G.pLen := by rcases gi.lens with e | e | e <;> rw [e] <;> decide
  have hn : nPk G = 2 * G.pLen + G.qLen := rfl
  have hsP : sPacked = 4096 := rfl
  obtain ⟨r0, r1, r2, r3, r4, r5⟩ := regs
  have e1 : (BitVec.ofNat 64 (nPk G)).toNat = nPk G := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have e2 : (BitVec.ofNat 64 G.pLen).toNat = G.pLen := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have e3 : (BitVec.ofNat 64 G.qLen).toNat = G.qLen := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have e5 : (BitVec.ofNat 64 G.wsW).toNat = G.wsW := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have W8 : wB G.pLen + G.wsW * 8 ≤ G.scrLen * 8 := by omega
  have P8 : sPacked + nPk G ≤ G.scrLen * 8 := by omega
  have sp : (cEntry G s).sp = σ.sp := by rw [State.withRegions_sp, State.callEntry_sp, gi.sp]
  have g := fun r hr => cEntry_gpr (G := G) (s := s) (r := r) hr
  have fitS : ∀ o, o < G.scrLen * 8 → (G.sa o).toNat = G.scr.toNat + o := fun o ho => by
    show (G.scr + BitVec.ofNat 64 o).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sp]; exact gi.pre.sp16
  · rw [State.withRegions_rd, g .a0 (by simp), g .a1 (by simp), r0, r1]
  · rw [State.withRegions_wr, g .a4 (by simp), g .a5 (by simp), r4, r5]
  · rw [g .a0 (by simp), g .a1 (by simp), g .a4 (by simp), g .a5 (by simp), r0, r1, r4, r5, e1, e5]
    exact gi.sdisj (.inl hsz) P8 W8
  · rw [g .a0 (by simp), g .a1 (by simp), r0, r1, e1, fitS _ (by omega)]; omega
  · rw [g .a4 (by simp), g .a5 (by simp), r4, r5, e5, fitS _ (by omega)]; omega
  · rw [g .a2 (by simp), g .a3 (by simp), r2, r3, e2, e3]; exact lv
  · rw [g .a1 (by simp), g .a2 (by simp), g .a3 (by simp), r1, r2, r3, e1, e2, e3]
  · rw [g .a2 (by simp), g .a5 (by simp), r2, r5, e2, e5, Spec.Dsa.scratchWords]; omega
  · rw [g .a4 (by simp), r4]; exact gi.al8 w8 (by omega)

/-- The check's regions are the search's. -/
theorem SS.cCovers (h : SS G STK0 σ c s) : Covers (cRd G ++ cWr G) (s.rd ++ s.wr) ∧ Covers (cWr G) s.wr := by
  have gi := h.gi
  obtain ⟨w63, wEq, wPos, w8⟩ := h.wsFit
  obtain ⟨hsz, _, _, n11, _⟩ := ck_sizes gi.lens
  have e1 : (BitVec.ofNat 64 (nPk G)).toNat = nPk G := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have e5 : (BitVec.ofNat 64 G.wsW).toNat = G.wsW := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have inS : G.rScr ∈ s.wr := by rw [gi.wr, gi.pre.wr, gi.hG]; simp
  have cw : Covers (cWr G) s.wr := (Covers.of_sub (rs' := [G.rScr]) fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨G.rScr, List.mem_singleton_self _, wB G.pLen, rfl,
      show wB G.pLen + (BitVec.ofNat 64 G.wsW).toNat * 8 ≤ G.scrLen * 8 by rw [e5]; omega⟩).trans
    (Covers.of_mem fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact inS)
  have cr : Covers (cRd G) s.wr := (Covers.of_sub (rs' := [G.rScr]) fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨G.rScr, List.mem_singleton_self _, sPacked, rfl,
      show sPacked + (BitVec.ofNat 64 (nPk G)).toNat ≤ G.scrLen * 8 by rw [e1]; omega⟩).trans
    (Covers.of_mem fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact inS)
  exact ⟨Covers.append_left cr.right cw.right, cw⟩

/-- The call of the check on the parameters `pk` at `sPacked`: its verdict
in `a0`'s low half, and memory changed only in the working space of the
functions we call and the stack. -/
theorem SS.checkCall_ok {code : Prog isa} {name : String} (ok : CheckOk code) (h : SS G STK0 σ c s)
    (regs : CArgs G s) {pk : List Byte} (hpk : Spec.Rsa.bytesAt s.mem (G.sa sPacked) (nPk G) = pk)
    {Q : State → Prop}
    (k : ∀ t, (∀ r ∈ preserved, t.gpr r = s.gpr r) → t.rd = s.rd → t.wr = s.wr → t.sp = s.sp →
      Frame [G.rs (wB G.pLen) (G.wsW * 8), rBelow σ STK0] s.mem t.mem →
      ((t.gpr .a0).setWidth 32).toNat = (if Spec.Dsa.checkParametersBytes G.pLen G.qLen pk then 1 else 0) → Q t) :
    WP isa (.call name code) s Q := by
  have gi := h.gi
  obtain ⟨w63, _⟩ := h.wsFit
  obtain ⟨_, _, _, n11, p11, q11, _⟩ := ck_sizes gi.lens
  have pin := h.cEntry_ckin regs
  obtain ⟨r0, r1, r2, r3, r4, r5⟩ := regs
  have e1 : (BitVec.ofNat 64 (nPk G)).toNat = nPk G := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have e5 : (BitVec.ofNat 64 G.wsW).toNat = G.wsW := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨hc, hw⟩ := h.cCovers
  refine WP.callAny ok.verified.1 (pre_of_ckin pin) hc hw (fun t rd wr sp f g post => ?_)
    (by have := ok.stack; simp only [STK0] at this; omega)
  have st := cpost_of_post post
  have hres : ckRes (cEntry G s) = Spec.Dsa.checkParametersBytes G.pLen G.qLen pk := by
    simp only [ckRes, State.withRegions_mem, State.callEntry_mem]
    rw [cEntry_gpr (by simp), cEntry_gpr (by simp), cEntry_gpr (by simp), cEntry_gpr (by simp), r0, r1, r2, r3, e1,
      hpk, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  refine k t g rd wr sp ?_ ?_
  · refine f.sub fun x hx => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨G.rs (wB G.pLen) (G.wsW * 8), by simp, by rw [e5]; exact fun _ h => h⟩
    · refine ⟨rBelow σ STK0, by simp, ?_⟩
      have := ok.stack
      have := gi.pre.spLo
      rw [gi.sp]
      exact Offset.sub_below _ (by omega) (by omega)
  · rw [State.withRegions_gpr] at st; rw [st, hres]

end

/-! ## p‖q‖g, checked -/

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- A claim the bytes hold, added. -/
theorem SS.consCl {STK : Nat} {σ s : State} (h : SS G STK σ c s) {o : Nat} {bs : List Byte}
    (e : Spec.Rsa.bytesAt s.mem (G.sa o) bs.length = bs) (ok : ClOk G (o, bs)) :
    SS G STK σ { c with cl := (o, bs) :: c.cl } s :=
  ⟨h.gi, h.sb.cons e, fun y hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ok
    · exact h.clOk y hy, h.arrs, h.liveOk, h.ksl, h.kslOk⟩

theorem kB_ge' (L : Nat) : 8192 ≤ kB L := by unfold kB pB; omega

/-- The claim at `x` copied to byte `k` of `sPacked`, the claims apart from it kept. -/
theorem copyP_vp {x k n : Nat} {kI : Int} (hkI : kI = (k : Int)) {bs : List Byte} (hs : (x, bs) ∈ c.cl)
    (hl : bs.length = n) (hn : 0 < n) (hn2 : n < 2048) (hx : x < 2048) (hk : k < 2048) (hxs : x + n ≤ sPacked)
    (hkn : k + n ≤ 4096) (hcl : ∀ y ∈ c.cl, Apart (sPacked + k) n y) :
    VP (St G c X) (copyN [scr .a0 x] (scrB .a1 sPacked ++ ([.addi .a1 .a1 kI] : List Instr)) n)
      (St G { c with cl := (sPacked + k, bs) :: c.cl } X) := by
  subst hkI
  have hP : sPacked = 4096 := rfl
  refine copyN_vp (c := fun _ => c) (o := sPacked + k) (fun σ s h => h.1) hn (by omega) (by kernel_rfl)
    (pro_scr_big (fun σ s h => h.1) hx (by decide) (by decide) hk hn2) (fun σ s h => ?_) (fun σ s h => ?_)
    fun σ s t ⟨h, x⟩ h' _ e => ⟨?_, x⟩
  · have := h.1.gi.wBig; have := h.1.gi.kBig; have := kB_ge' G.pLen; have := h.1.gi.hEnd_le
    exact ⟨by simp only [hEnd, fSave] at *; omega, .inl (by simp only [List.length_replicate]; omega),
      by simp only [List.length_replicate]; omega⟩
  · have gi := h.1.gi
    have := gi.wBig; have := gi.kBig; have := kB_ge' G.pLen
    have fit := gi.scrFit
    refine ⟨fun i hi => by rw [GP.sa_add]; exact gi.inRdWr (o := x + i) (n := 1) (by omega), ?_⟩
    exact Offset.sep _ (.inr (by omega)) (by omega) (by omega)
  · have hf : c.cl.filter (fun y => decide (Apart (sPacked + k) n y)) = c.cl :=
      List.filter_eq_self.mpr fun y hy => decide_eq_true (hcl y hy)
    simp only [hf] at h'
    have b := h.sb _ hs
    simp only [hl] at b
    have := h'.gi.wBig; have := h'.gi.kBig; have := kB_ge' G.pLen; have := h'.gi.hEnd_le
    refine h'.consCl (by rw [hl, e, b]) ⟨by simp only [hEnd, fSave] at *; omega, .inl (by rw [hl]; omega),
      by rw [hl]; omega⟩

/-- The check's arguments. -/
theorem cargs_vp :
    VP (St G c X) (.block (scrB .a0 sPacked ++ ([.li .a1 (2 * (G.pLen : Int) + G.qLen), .li .a2 G.pLen,
        .li .a3 G.qLen] : List Instr) ++ scrB .a4 (wB G.pLen) ++ wsLen .a5 G.pLen))
      (fun σ s => St G c X σ s ∧ CArgs G s) := by
  refine VP.pub (SS.pub (c := fun _ => c) fun σ s h => h.1) [] ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64
    (Taint.ofRegs [.s6]) (.block (scrB .a0 sPacked ++ ([.li .a1 (2 * (G.pLen : Int) + G.qLen), .li .a2 G.pLen,
        .li .a3 G.qLen] : List Instr) ++ scrB .a4 (wB G.pLen) ++ wsLen .a5 G.pLen)), by kernel_rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ => ?_
  have gi := h.gi
  obtain ⟨_, _, _, n11, p11, q11, _, w7, w0⟩ := ck_sizes (G := G) gi.lens
  obtain ⟨w63, wEq, wPos, w8⟩ := h.wsFit
  have hn : nPk G = 2 * G.pLen + G.qLen := rfl
  have e1 : (2 * (G.pLen : Int) + G.qLen) = ((2 * G.pLen + G.qLen : Nat) : Int) := by omega
  rw [e1, List.append_assoc, List.append_assoc]
  refine scrB_ok (by decide) gi.s6 (by decide) (by decide) fun t₀ K₀ m₀ sp₀ v₀ => ?_
  have h₀ := h.of_keep K₀ m₀ sp₀
  simp only [List.cons_append, List.nil_append]
  refine wp_li (by omega) fun s₁ u₁ => wp_li p11 fun s₂ u₂ => wp_li q11 fun s₃ u₃ => ?_
  have h₃ := ((h₀.of_upd u₁ (by decide)).of_upd u₂ (by decide)).of_upd u₃ (by decide)
  refine scrB_ok (by decide) h₃.gi.s6 w0 w7 fun t₄ K₄ m₄ sp₄ v₄ => ?_
  have h₄ := h₃.of_keep K₄ m₄ sp₄
  simp only [wsLen]
  refine h₄.ldK (o := fScrLen) (by decide) (by decide)
    (h₄.gi.fixedV (v := BitVec.ofNat 64 G.scrLen) (by simp [fixedWords])) (t := .a5) (by decide)
    fun s₅ h₅ u₅ => ?_
  refine WP.cons exec_lui ?_
  have u₆ := Upd.write s₅ .t3 (sext32 (BitVec.ofNat 20 (wB G.pLen / 4096) ++ (0 : BitVec 12)))
  have h₆ := h₅.of_upd u₆ (by decide)
  refine wp_srl (by decide) fun s₇ u₇ => ?_
  have h₇ := h₆.of_upd u₇ (by decide)
  refine wp_sub fun s₈ u₈ => WP.block_nil ⟨⟨h₇.of_upd u₈ (by decide), x⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      K₄.gpr (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), v₀]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      K₄.gpr (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      K₄.gpr (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      K₄.gpr (by decide), u₃.gpr]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), v₄]
  · have lv : sext32 (BitVec.ofNat 20 (wB G.pLen / 4096) ++ (0 : BitVec 12)) = BitVec.ofNat 64 (wB G.pLen) := by
      rw [luiv _ w7, show 4096 * (wB G.pLen / 4096) = wB G.pLen by omega]
    have := gi.scrFit
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₇.gpr, u₆.gpr, lv, shr3 (by omega),
      BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]

/-- The call of the check on the claim `pk` at `sPacked`. -/
theorem checkCall_vp {code : Prog isa} {name : String} (ok : CheckOk code) {pk : List Byte}
    (hpk : (sPacked, pk) ∈ c.cl) (hpkl : pk.length = nPk G)
    (hcl : ∀ x ∈ c.cl, Apart (wB G.pLen) (G.wsW * 8) x) :
    VP (fun σ s => St G c X σ s ∧ CArgs G s) (.call name code)
      (fun σ t => St G c X σ t ∧
        ((t.gpr .a0).setWidth 32).toNat = (if Spec.Dsa.checkParametersBytes G.pLen G.qLen pk then 1 else 0)) := by
  have bytes : ∀ σ s, SS G STK0 σ c s → Spec.Rsa.bytesAt s.mem (G.sa sPacked) (nPk G) = pk := fun σ s h => by
    have := h.sb _ hpk; rw [hpkl] at this; exact this
  refine VP.of_ct (fun σ₁ σ₂ => ?_) fun σ s ⟨⟨h, x⟩, regs⟩ => ?_
  · refine (RelCT.call ok.verified.1 ok.verified.2.1 (cRd G) (cWr G) fun s₁ s₂ ⟨⟨⟨h₁, _⟩, g₁⟩, ⟨⟨h₂, _⟩, g₂⟩⟩ =>
      ?_).mono (fun _ _ h => h) fun _ _ _ => trivial
    have p₁ := pre_of_ckin (h₁.cEntry_ckin g₁)
    have p₂ := pre_of_ckin (h₂.cEntry_ckin g₂)
    obtain ⟨cr₁, cw₁⟩ := h₁.cCovers
    obtain ⟨cr₂, cw₂⟩ := h₂.cCovers
    obtain ⟨a0, a1, a2, a3, a4, a5⟩ := g₁
    obtain ⟨b0, b1, b2, b3, b4, b5⟩ := g₂
    refine ⟨p₁, p₂, cpub_of ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, cr₁, cw₁, cr₂, cw₂⟩
    · have e₁ : s₁.sp = G.sp := by rw [h₁.gi.sp, ← h₁.gi.hG]; rfl
      have e₂ : s₂.sp = G.sp := by rw [h₂.gi.sp, ← h₂.gi.hG]; rfl
      show s₁.sp = s₂.sp
      rw [e₁, e₂]
    · rw [cEntry_gpr (by simp), cEntry_gpr (by simp), a0, b0]
    · rw [cEntry_gpr (by simp), cEntry_gpr (by simp), a1, b1]
    · rw [cEntry_gpr (by simp), cEntry_gpr (by simp), a2, b2]
    · rw [cEntry_gpr (by simp), cEntry_gpr (by simp), a3, b3]
    · rw [cEntry_gpr (by simp), cEntry_gpr (by simp), a4, b4]
    · rw [cEntry_gpr (by simp), cEntry_gpr (by simp), a5, b5]
    · obtain ⟨_, _, _, n11, _⟩ := ck_sizes (G := G) h₁.gi.lens
      have e1 : (BitVec.ofNat 64 (nPk G)).toNat = nPk G := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [State.withRegions_mem, State.callEntry_mem]
      rw [cEntry_gpr (by simp), cEntry_gpr (by simp), cEntry_gpr (by simp), cEntry_gpr (by simp), a0, a1, b0, b1, e1,
        bytes _ _ h₁, bytes _ _ h₂]
  refine h.checkCall_ok (name := name) ok regs (bytes _ _ h) fun t g rd wr sp f st => ⟨⟨?_, x⟩, st⟩
  have big := h.gi.wBig
  have kb := h.gi.kBig
  have hE := h.gi.hEnd_le
  obtain ⟨w63, wEq, wPos, w8⟩ := h.wsFit
  have l := lay_ok h.lens
  have := kB_ge' G.pLen
  exact h.of_scrs (keep_of_preserved g rd wr) sp (os := [(wB G.pLen, G.wsW * 8)])
    (fun p hp => by
      rw [List.mem_singleton] at hp; subst hp
      exact ⟨by simp only [hEnd, fSave] at hE ⊢; omega, .inr (Nat.le_refl _),
        by simp only [List.length_replicate]; omega⟩)
    f (cl' := c.cl) (fun y hy => .inl ⟨hy, fun p hp => by rw [List.mem_singleton] at hp; subst hp; exact hcl y hy⟩)

/-- The stage after the check. -/
abbrev ckCfg (c : Cfg) (pk : List Byte) (ok : Bool) : Cfg :=
  if ok then ({ c with cl := (sPacked, pk) :: c.cl }).setV fStatus 1 else { c with cl := (sPacked, pk) :: c.cl }

/-- The verdict, zero-extended, compared with 1. -/
theorem verdict_vp {c' : Cfg} {b : Bool} :
    VP (fun σ t => St G c' X σ t ∧ ((t.gpr .a0).setWidth 32).toNat = (if b then 1 else 0))
      (.block [.shift .sll .d .a0 .a0 32, .shift .srl .d .a0 .a0 32, .addi .t2 .a0 (-1)])
      (fun σ t => St G c' X σ t ∧ isa.eval (.zero .t2) t = some b) := by
  refine VP.pub (SS.pub (c := fun _ => c') fun σ s h => h.1.1) []
    ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6])
      (.block [.shift .sll .d .a0 .a0 32, .shift .srl .d .a0 .a0 32, .addi .t2 .a0 (-1)]), by kernel_rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨⟨h, x⟩, a0⟩ => ?_
  refine wp_sll (by decide) fun s₁ u₁ => wp_srl (by decide) fun s₂ u₂ => wp_subi (imm := 1) (by decide)
    fun t u => WP.block_nil ⟨⟨((h.of_upd u₁ (by decide)).of_upd u₂ (by decide)).of_upd u (by decide), x⟩, ?_⟩
  have hv : s₂.gpr .a0 = BitVec.ofNat 64 (if b then 1 else 0) := by rw [u₂.gpr, u₁.gpr, zext32, a0]
  rw [eval_zero, u.gpr, hv, sub_beq_zero]
  cases b <;> decide

/-- p (at `sPBE`), q (at `sQ`) and g (at `sG`) side by side at `sPacked`,
checked: `fStatus` := 1 if `checkParametersBytes` accepts them. -/
theorem checkPart_vp {g : Geo} (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hck : CheckOk g.checkCode)
    {pB qB gB : List Byte} (hP : (sPBE, pB) ∈ c.cl) (hQ : (sQ, qB) ∈ c.cl) (hG : (sG, gB) ∈ c.cl)
    (hPl : pB.length = G.pLen) (hQl : qB.length = G.qLen) (hGl : gB.length = G.pLen)
    (hcl : ∀ x ∈ c.cl, x.1 + x.2.length ≤ sPacked) :
    VP (St G c X) g.checkPart
      (St G (ckCfg c (pB ++ qB ++ gB) (Spec.Dsa.checkParametersBytes G.pLen G.qLen (pB ++ qB ++ gB))) X) := by
  by_cases l : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384
  swap
  · exact VP.of_false fun σ s h => l h.1.lens
  obtain ⟨hsz, lv, hE, n11, p11, q11, q0, w7, w0⟩ := ck_sizes (G := G) l
  have hp0 : 0 < G.pLen := by rcases l with e | e | e <;> rw [e] <;> decide
  have hq32 : G.qLen ≤ 32 := by simp only [GP.qLen, Spec.Dsa.generationQLen]; split <;> omega
  have hp384 : G.pLen ≤ 384 := by omega
  have e1 : sPacked = 4096 := rfl
  have e2 : sPBE = 960 := rfl
  have e3 : sQ = 512 := rfl
  have e4 : sG = 1728 := rfl
  unfold Geo.checkPart
  rw [hp, hq]
  -- The copies.
  refine VP.seq (copyP_vp (k := 0) rfl hP hPl hp0 p11 (by omega) (by omega) (by omega) (by omega)
    fun x hx => .inl (by simpa using hcl x hx)) ?_
  refine VP.seq (copyP_vp (k := G.pLen) rfl (List.mem_cons_of_mem _ hQ) hQl q0 q11 (by omega) p11 (by omega)
    (by omega) fun x hx => ?_) ?_
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact .inl (by simp only [hPl]; omega)
    · exact .inl (by have := hcl x hx; omega)
  refine VP.seq (copyP_vp (k := G.pLen + G.qLen) (by omega)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hG)) hGl hp0 p11 (by omega) (by omega) (by omega) (by omega)
    fun x hx => ?_) ?_
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact .inl (by simp only [hQl]; omega)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact .inl (by simp only [hPl]; omega)
    · exact .inl (by have := hcl x hx; omega)
  -- p‖q‖g, as one claim.
  have hpkl : (pB ++ qB ++ gB).length = nPk G := by simp only [List.length_append, hPl, hQl, hGl, nPk]; omega
  have join : ∀ σ s, SS G STK0 σ { c with cl := (sPacked + (G.pLen + G.qLen), gB) :: (sPacked + G.pLen, qB) ::
      (sPacked + 0, pB) :: c.cl } s → SS G STK0 σ { c with cl := (sPacked, pB ++ qB ++ gB) :: c.cl } s :=
    fun σ s h => by
    have bp := h.sb (sPacked + 0, pB) (by simp)
    have bq := h.sb (sPacked + G.pLen, qB) (by simp)
    have bg := h.sb (sPacked + (G.pLen + G.qLen), gB) (by simp)
    simp only [Nat.add_zero] at bp bq bg
    rw [hPl] at bp
    rw [hQl] at bq
    rw [hGl] at bg
    have hc : Spec.Rsa.bytesAt s.mem (G.sa sPacked) (pB ++ qB ++ gB).length = pB ++ qB ++ gB := by
      rw [List.length_append, List.length_append, hPl, hQl, hGl, VG.Proof.Dsa.Generation.bytesAt_append,
        VG.Proof.Dsa.Generation.bytesAt_append, VG.Proof.Bignum.off, VG.Proof.Bignum.off, GP.sa_add, GP.sa_add,
        bp, bq, bg]
    have := h.gi.wBig; have := h.gi.kBig; have := kB_ge' G.pLen
    exact (h.mono (c' := c) (fun o ho => ⟨ho, rfl⟩) (fun y hy => by simp [hy]) (fun j hj => ⟨hj, rfl⟩)
      (fun d hd => ⟨hd, rfl⟩)).consCl hc ⟨by simp only [hEnd, fSave] at hE ⊢; omega,
        .inl (by rw [hpkl]; omega), by rw [hpkl]; omega⟩
  refine VP.seq ((cargs_vp (c := { c with cl := (sPacked + (G.pLen + G.qLen), gB) :: (sPacked + G.pLen, qB) ::
      (sPacked + 0, pB) :: c.cl }) (X := X)).mono (G' := fun σ s => St G { c with cl := (sPacked, pB ++ qB ++ gB) ::
        c.cl } X σ s ∧ CArgs G s) (fun _ _ h => h) fun σ s ⟨⟨h, x⟩, a⟩ => ⟨⟨join σ s h, x⟩, a⟩) ?_
  -- The check.
  refine VP.seq (checkCall_vp (c := { c with cl := (sPacked, pB ++ qB ++ gB) :: c.cl }) hck (by simp) hpkl
    fun y hy => .inl (by
      have := lay_ok l
      have := kB_ge' G.pLen
      rcases List.mem_cons.mp hy with rfl | hy
      · rw [hpkl]; omega
      · have := hcl y hy; omega)) ?_
  generalize hbv : Spec.Dsa.checkParametersBytes G.pLen G.qLen (pB ++ qB ++ gB) = b
  refine VP.seq verdict_vp ?_
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
  · cases b
    · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z
    · exact stImm_vp (c := fun _ => { c with cl := (sPacked, pB ++ qB ++ gB) :: c.cl }) (o := fStatus) (v := 1)
        (fun σ s h => h.1.1.1) (by decide) varOk_fStatus fun σ s t h h' _ => ⟨h', h.1.1.2⟩
  · cases b
    · exact VP.block_nil fun σ s h => h.1.1
    · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z

end

/-! ## The generator and the check -/

/-- The candidates of the window from `u`, as the spec reads them. -/
abbrev hsOf (G : GP) (u : Nat) : List Nat :=
  Proof.Dsa.Generation.windowCandidates G.pLen Spec.Dsa.generatorAttempts (G.randB.drop u)

/-- The stage after the generator and the check, from the cursor `u`, `p`
and `q`: as `refillAttempt` after `p`, `fUsed` past the candidates read and
`fStatus` 1 with the packed parameters if they are valid; without a
generator, the window's octets consumed if the tape held it whole, and
`fStatus` 0 if not. -/
def gcCfg (c : Cfg) (G : GP) (u pv qv : Nat) : Cfg :=
  match Spec.Dsa.generator pv qv (hsOf G u) with
  | some g =>
    if Spec.Dsa.parametersValid ⟨pv, qv, g⟩ then
      ({ c.setV fUsed (BitVec.ofNat 64 (u + G.pLen * Proof.Dsa.Generation.generatorCount pv qv (hsOf G u))) with
        cl := (sPacked, Spec.Dsa.encodeParams G.pLen G.qLen ⟨pv, qv, g⟩) :: c.cl }).setV fStatus 1
    else c.setV fUsed (BitVec.ofNat 64 (u + G.pLen * Proof.Dsa.Generation.generatorCount pv qv (hsOf G u)))
  | none =>
    if Spec.Dsa.generatorAttempts * G.pLen ≤ (G.randB.drop u).length then
      c.setV fUsed (BitVec.ofNat 64 (u + Spec.Dsa.generatorAttempts * G.pLen))
    else (c.setV fUsed (BitVec.ofNat 64 (u + G.pLen * Proof.Dsa.Generation.generatorCount pv qv (hsOf G u)))).setV
      fStatus 0

theorem gList_zero (G : GP) (u : Nat) : G.gList u 0 = hsOf G u := by
  simp [GP.gList, hsOf, Proof.Dsa.Generation.windowCandidates, GP.winB]

/-- Without a generator, every candidate is read. -/
theorem count_none {p q : Nat} : ∀ {hs : List Nat}, Spec.Dsa.generator p q hs = none →
    Proof.Dsa.Generation.generatorCount p q hs = hs.length
  | [], _ => rfl
  | h :: hs, e => by
    rw [Proof.Dsa.Generation.generator_cons'] at e
    cases hh : Proof.Dsa.Generation.generatorHit p q h
    · rw [hh] at e
      simp only [Bool.false_eq_true, ↓reduceIte] at e
      simp only [Proof.Dsa.Generation.generatorCount, hh, Bool.false_eq_true, ↓reduceIte, count_none e,
        List.length_cons]
    · rw [hh] at e; simp at e

/-- A window the tape held whole has `generatorAttempts` candidates. -/
theorem count_none_full {G : GP} {u pv qv : Nat} (hp0 : 0 < G.pLen)
    (hn : Spec.Dsa.generator pv qv (hsOf G u) = none)
    (hf : Spec.Dsa.generatorAttempts * G.pLen ≤ (G.randB.drop u).length) :
    G.pLen * Proof.Dsa.Generation.generatorCount pv qv (hsOf G u) = Spec.Dsa.generatorAttempts * G.pLen := by
  rw [count_none hn]
  simp only [hsOf, Proof.Dsa.Generation.windowCandidates, Spec.Dsa.generationChunks, List.length_map,
    List.length_range, List.length_take, Nat.min_eq_left hf, Nat.mul_div_cancel _ hp0, Nat.mul_comm]

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The words the search for g sets. -/
abbrev gKeys : List Nat := [fH, fHLeft, fHStart, fFull, fG]

theorem gFin_V {u : Nat} (res : Option Nat) (n : Nat) {o : Nat} (ho : o ∉ gKeys) :
    o ∈ c.LS → o ∈ (gFin c G u res n).LS ∧ (gFin c G u res n).V o = c.V o := by
  simp only [gKeys, List.mem_cons, List.not_mem_nil, or_false, not_or] at ho
  obtain ⟨a, b, d, e, f⟩ := ho
  intro hm
  cases res <;> simp [gFin, upd, a, b, d, e, f, hm]

/-- A stage over the search for g's words as one over `c`'s, with the same
`fUsed` word. -/
theorem SS.ofGp {σ s : State} {u : Nat} {res : Option Nat} {n : Nat} {cl cl' : Claims} {vU : BitVec 64}
    (hfr : ∀ o ∈ gKeys, o ∉ c.LS) (h : SS G STK0 σ { (gFin c G u res n).setV fUsed vU with cl := cl } s)
    (hcl : ∀ x ∈ cl', x ∈ cl) : SS G STK0 σ { c.setV fUsed vU with cl := cl' } s := by
  have key : ∀ o ∈ c.LS, o ∈ (gFin c G u res n).LS ∧ (gFin c G u res n).V o = c.V o := fun o ho =>
    gFin_V res n (fun hk => hfr o hk ho) ho
  refine h.mono (fun o ho => ?_) hcl (fun j hj => ⟨?_, ?_⟩) (fun d hd => ⟨?_, ?_⟩)
  · simp only [List.mem_cons] at ho ⊢
    rcases ho with rfl | ho
    · exact ⟨.inl rfl, by simp [upd]⟩
    · refine ⟨.inr (key o ho).1, ?_⟩
      simp only [upd]; split
      · rfl
      · exact (key o ho).2
  all_goals cases res <;> first | exact hj | exact hd | rfl

/-- The same, with the same `fStatus` word. -/
theorem SS.ofGpS {σ s : State} {u : Nat} {res : Option Nat} {n : Nat} {cl cl' : Claims} {vU v : BitVec 64}
    (hfr : ∀ o ∈ gKeys, o ∉ c.LS)
    (h : SS G STK0 σ (({ (gFin c G u res n).setV fUsed vU with cl := cl }).setV fStatus v) s)
    (hcl : ∀ x ∈ cl', x ∈ cl) : SS G STK0 σ (({ c.setV fUsed vU with cl := cl' }).setV fStatus v) s := by
  have key : ∀ o ∈ c.LS, o ∈ (gFin c G u res n).LS ∧ (gFin c G u res n).V o = c.V o := fun o ho =>
    gFin_V res n (fun hk => hfr o hk ho) ho
  refine h.mono (fun o ho => ?_) hcl (fun j hj => ⟨?_, ?_⟩) (fun d hd => ⟨?_, ?_⟩)
  · simp only [List.mem_cons] at ho ⊢
    rcases ho with rfl | rfl | ho
    · exact ⟨.inl rfl, by simp [upd]⟩
    · exact ⟨.inr (.inl rfl), by simp [upd]⟩
    · refine ⟨.inr (.inr (key o ho).1), ?_⟩
      simp only [upd]; split
      · rfl
      · split
        · rfl
        · exact (key o ho).2
  all_goals cases res <;> first | exact hj | exact hd | rfl

end

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The generator over the window from the cursor `u` and, with one, the
check of p‖q‖g: the stage `gcCfg`, the generator part of `refillAttempt`.
The search reads `fUsed`; `c`'s other words, its claims (but at `sPacked`)
and its arrays are kept. -/
theorem gCheck_vp {g : Geo} (hg : g.pLen = G.pLen) (hgq : g.qLen = G.qLen) (cert : CertC G.pLen G.qLen)
    (hck : CheckOk g.checkCode) {u pv qv : Nat} (R : GReq G c pv ((pv - 1) / qv))
    (hQc : (sQ, Spec.Rsa.i2osp qv G.qLen) ∈ c.cl) (hqv : qv < 256 ^ G.qLen) (hu : u ≤ G.randLen)
    (hU : fUsed ∈ c.LS) (hUv : c.V fUsed = BitVec.ofNat 64 u) (hfr : ∀ o ∈ gKeys, o ∉ c.LS)
    (hcl : ∀ x ∈ c.cl, x.1 + x.2.length ≤ sPacked) :
    VP (St G c X) g.gCheck (St G (gcCfg c G u pv qv) X) := by
  by_cases l : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384
  swap
  · exact VP.of_false fun σ s h => l h.1.lens
  by_cases hRL : G.randB.length = G.randLen
  swap
  · exact VP.of_false fun σ s h => hRL h.1.gi.randB_len
  obtain ⟨hsz, lv, hE, n11, p11, q11, q0, w7, w0⟩ := ck_sizes (G := G) l
  have hp0 : 0 < G.pLen := by rcases l with e | e | e <;> rw [e] <;> decide
  have hp384 : G.pLen ≤ 384 := by omega
  unfold Geo.gCheck
  refine VP.seq (gPart_vp hg hgq cert R hu hRL rfl hU hUv) ?_
  simp only [gpCfg, nRead, gList_zero, gcCfg]
  generalize hn : Proof.Dsa.Generation.generatorCount pv qv (hsOf G u) = n
  rcases hgv : Spec.Dsa.generator pv qv (hsOf G u) with _ | gv
  · -- No g: ran out if the window was cut short.
    have fGv : ∀ vU : BitVec 64, ((gFin c G u none n).setV fUsed vU).V fG = BitVec.ofNat 64 2 := fun vU => by
      simp [gFin, upd, fUsed, fG]
    refine VP.seq (cmpF_vp (c := fun _ => (gFin c G u none n).setV fUsed (BitVec.ofNat 64 (u + G.pLen * n)))
      (x := BitVec.ofNat 64 2) (o := fG) (v := 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.gi.slotV (by simp [gFin])).trans (fGv _))
      (Q := fun σ t => St G ((gFin c G u none n).setV fUsed (BitVec.ofNat 64 (u + G.pLen * n))) X σ t ∧
        isa.eval (.zero .t2) t = some false) fun σ s t hs h' _ e => ⟨⟨h', hs.2⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) ?_
    have fFv : ((gFin c G u none n).setV fUsed (BitVec.ofNat 64 (u + G.pLen * n))).V fFull =
        BitVec.ofNat 64 (G.full u) := by simp [gFin, upd, fUsed, fG, fFull, fH, fHLeft]
    refine VP.seq (ld_vp (c := fun _ => (gFin c G u none n).setV fUsed (BitVec.ofNat 64 (u + G.pLen * n)))
      (r := .t2) (o := fFull) (fun σ s h => h.1.1.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.1.1.gi.slotV (by simp [gFin])).trans fFv)
      (Q := fun σ t => St G ((gFin c G u none n).setV fUsed (BitVec.ofNat 64 (u + G.pLen * n))) X σ t ∧
        t.gpr .t2 = BitVec.ofNat 64 (G.full u)) fun σ s t hs h' u' => ⟨⟨h', hs.1.1.2⟩, u'.gpr⟩) ?_
    have hdl : (G.randB.drop u).length = G.randLen - u := by rw [List.length_drop, hRL]
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2]) ?_ ?_
    · by_cases hf : Spec.Dsa.generatorAttempts * G.pLen ≤ (G.randB.drop u).length
      · refine VP.of_false fun σ s ⟨⟨_, t2⟩, z⟩ => ?_
        rw [eval_zero, t2, show G.full u = 1 by simp only [GP.full]; rw [hdl] at hf; simp [hf]] at z
        simp at z
      · simp only [hf, ↓reduceIte]
        exact stImm_vp (c := fun _ => (gFin c G u none n).setV fUsed (BitVec.ofNat 64 (u + G.pLen * n)))
          (fun σ s h => h.1.1.1) (by decide) varOk_fStatus fun σ s t hs h' _ =>
            ⟨SS.ofGpS (cl := ((gFin c G u none n).setV fUsed (BitVec.ofNat 64 (u + G.pLen * n))).cl) hfr h'
              (fun y hy => hy), hs.1.1.2⟩
    · by_cases hf : Spec.Dsa.generatorAttempts * G.pLen ≤ (G.randB.drop u).length
      · simp only [hf, ↓reduceIte]
        have e : G.pLen * n = Spec.Dsa.generatorAttempts * G.pLen := by rw [← hn]; exact count_none_full hp0 hgv hf
        rw [e] at *
        exact VP.block_nil fun σ s ⟨⟨⟨h, x⟩, _⟩, _⟩ =>
          ⟨SS.ofGp (cl := ((gFin c G u none n).setV fUsed (BitVec.ofNat 64 (u + Spec.Dsa.generatorAttempts * G.pLen))).cl)
            hfr h (fun y hy => hy), x⟩
      · refine VP.of_false fun σ s ⟨⟨_, t2⟩, z⟩ => ?_
        rw [eval_zero, t2, show G.full u = 0 by simp only [GP.full]; rw [hdl] at hf; simp [hf]] at z
        simp at z
  · -- g: the check.
    have hgb := VG.Proof.Dsa.Generation.generator_bounds (by have := R.hp2; omega : 0 < pv) (hsOf G u) hgv
    let D : Cfg := (gFin c G u (some gv) n).setV fUsed (BitVec.ofNat 64 (u + G.pLen * n))
    have fGv : D.V fG = BitVec.ofNat 64 1 := by simp [D, gFin, upd, fUsed, fG]
    refine VP.seq (cmpF_vp (c := fun _ => D) (x := BitVec.ofNat 64 1) (o := fG) (v := 1) (fun σ s h => h.1)
      (by decide) (by decide) (by decide) (fun σ s h => (h.1.gi.slotV (by simp [gFin])).trans fGv)
      (Q := fun σ t => St G D X σ t ∧ isa.eval (.zero .t2) t = some true)
      fun σ s t hs h' _ e => ⟨⟨h', hs.2⟩, by rw [e]; rfl⟩) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z)
    have hpl8 : (256 : Nat) ^ G.pLen = 2 ^ (8 * G.pLen) := by rw [Nat.pow_mul]
    have hpk : Spec.Rsa.i2osp pv G.pLen ++ Spec.Rsa.i2osp qv G.qLen ++ Spec.Rsa.i2osp gv G.pLen =
        Spec.Dsa.encodeParams G.pLen G.qLen ⟨pv, qv, gv⟩ := by
      simp only [Spec.Dsa.encodeParams, VG.Proof.Dsa.encodeBE_i2osp]
    have hok : Spec.Dsa.checkParametersBytes G.pLen G.qLen
        (Spec.Rsa.i2osp pv G.pLen ++ Spec.Rsa.i2osp qv G.qLen ++ Spec.Rsa.i2osp gv G.pLen) =
        decide (Spec.Dsa.parametersValid ⟨pv, qv, gv⟩) := by
      rw [hpk]
      exact VG.Proof.Dsa.Generation.check_encodedParams lv R.hpv hqv (Nat.lt_trans hgb.2 R.hpv)
    refine (checkPart_vp (c := D) (X := X) hg hgq hck (pB := Spec.Rsa.i2osp pv G.pLen)
      (qB := Spec.Rsa.i2osp qv G.qLen) (gB := Spec.Rsa.i2osp gv G.pLen) (by simp [D, gFin, R.hPc])
      (by simp [D, gFin, hQc]) (by simp [D, gFin]) (VG.Proof.Rsa.i2osp_length _ _) (VG.Proof.Rsa.i2osp_length _ _)
      (VG.Proof.Rsa.i2osp_length _ _) (fun x hx => ?_)).mono (fun σ s h => h.1.1) fun σ s ⟨h, x⟩ => ⟨?_, x⟩
    · simp only [D, gFin, List.mem_cons] at hx
      rcases hx with rfl | hx
      · simp only [VG.Proof.Rsa.i2osp_length, sG, sPacked]; omega
      · exact hcl x hx
    rw [hok, hpk] at h
    by_cases hv : Spec.Dsa.parametersValid ⟨pv, qv, gv⟩
    · simp only [hv, decide_true, ckCfg, ↓reduceIte] at h
      simp only [hv, ↓reduceIte]
      exact SS.ofGpS hfr h fun y hy => by
        rcases List.mem_cons.mp hy with rfl | hy
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy)
    · simp only [hv, decide_false, ckCfg, Bool.false_eq_true, ↓reduceIte] at h
      simp only [hv, ↓reduceIte]
      exact SS.ofGp hfr h fun y hy => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy)

end

end VG.Proof.Dsa.RISCV64.PSearch

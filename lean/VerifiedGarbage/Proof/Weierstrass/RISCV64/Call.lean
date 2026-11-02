module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.FieldRV
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Mont.Read

/-!
# Calls of the Montgomery arithmetic's functions, on RISC-V

`callOp f body o a b` (`Impl/Weierstrass/RISCV64.lean`) calls the function
`f`, whose code is `body`, on the working space in `s0` and the offsets `o`,
`a` and `b` (`callOp_ok`): from a state whose writable regions include the
`8192` bytes of the working space (`WsReg`), the callee-saved registers, the
regions and the stack pointer stay, and only the number at `o` and the
functions' own working space change (`CallKeep`), by what the contract by
register (`Proof/Weierstrass/RISCV64/FieldRV.lean`) says. `mulCall_ok`,
`addCall_ok` and `subCall_ok` are the calls of a field's functions, for any
field whose code meets those contracts (`FieldOk`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Weierstrass.RISCV64
open VG.Proof.Mont
open VG.Impl.Weierstrass.Mont (numAt Keeps Modulus ownAt ownBytes)

/-- The working space: its base in `s0`, aligned, its `8192` bytes writable,
not wrapping around. -/
structure WsReg (s : State) (base : Addr) : Prop where
  s0 : s.gpr .s0 = base
  wr : (⟨base, 8192⟩ : Region) ∈ s.wr
  nowrap : base.toNat + 8192 ≤ 2 ^ 64
  al : base.toNat % 8 = 0

/-- A field whose code meets the contracts by register, without frames. -/
structure FieldOk (F : Field) : Prop where
  mul : Meets F.mul (mulRV F.S)
  add : Meets F.add (addRV F.S)
  sub : Meets F.sub (subRV F.S)
  nmul : F.mul.noFrames = true
  nadd : F.add.noFrames = true
  nsub : F.sub.noFrames = true

/-- The registers, regions and stack pointer a call keeps. -/
structure Kp (s s' : State) : Prop where
  gpr : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Kp.refl (s : State) : Kp s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Kp.trans {s₁ s₂ s₃ : State} (h₁ : Kp s₁ s₂) (h₂ : Kp s₂ s₃) : Kp s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem Kp.of_upd {s s' : State} {d : Reg} {v : BitVec 64} (h : Upd s s' d v) (hd : d ∉ preserved := by decide) :
    Kp s s' :=
  ⟨fun r hr => h.other r fun e => hd (e ▸ hr), h.rd, h.wr, h.sp⟩

theorem Kp.of_mupd {s s' : State} {m : Mem} (h : Mupd s s' m) : Kp s s' :=
  ⟨fun r _ => by rw [h.gpr], h.rd, h.wr, h.sp⟩

theorem WsReg.of_kp {s s' : State} {base : Addr} (h : WsReg s base) (k : Kp s s') : WsReg s' base :=
  ⟨(k.gpr _ (by decide)).trans h.s0, k.wr ▸ h.wr, h.nowrap, h.al⟩

/-- The own working space of `k`-word functions, as a range of offsets. -/
abbrev own (k : Nat) : Nat := ownAt k

/-- What a call writing `[o]` keeps: `Kp`, and the memory but `[o]` and the
functions' own working space. -/
structure CallKeep (k : Nat) (base : Addr) (o : Nat) (s s' : State) : Prop where
  kp : Kp s s'
  mem : Outs base [(o, 8 * k), (own k, 64 * k)] s.mem s'.mem

/-! ## Offsets past 2047 (`ldAt`, `sdAt`, `liAt`) -/

section At
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem ofNat_2047_add {v : Nat} (h : 2047 ≤ v) :
    BitVec.ofNat 64 2047 + BitVec.ofNat 64 (v - 2047) = BitVec.ofNat 64 v := by
  rw [BitVec.ofNat_add_ofNat, show 2047 + (v - 2047) = v by omega]

theorem add_2047_add (x : BitVec 64) {v : Nat} (h : 2047 ≤ v) :
    x + BitVec.ofNat 64 2047 + BitVec.ofNat 64 (v - 2047) = x + BitVec.ofNat 64 v := by
  rw [BitVec.add_assoc, ofNat_2047_add h]

/-- Two writes of the same register are one. -/
theorem _root_.VG.RISCV64.Steps.Upd.twice {s₁ s₂ : State} {d : Reg} {v w : BitVec 64} (u₁ : Upd s s₁ d v) (u₂ : Upd s₁ s₂ d w) :
    Upd s s₂ d w :=
  ⟨u₂.gpr, fun r hr => by rw [u₂.other r hr, u₁.other r hr], by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd],
    by rw [u₂.wr, u₁.wr], by rw [u₂.sp, u₁.sp]⟩

/-- `rd = v` (`liAt`). -/
theorem wp_liAt {d : Reg} {v : Nat} (h : v < 4095)
    (k : ∀ s', Upd s s' d (BitVec.ofNat 64 v) → WP isa (.block is) s' Q) :
    WP isa (.block (liAt d v ++ is)) s Q := by
  unfold liAt
  split
  · exact wp_li (by omega) k
  · refine wp_li (imm := 2047) (by decide) fun s₁ u₁ => wp_addi (by omega) fun s₂ u₂ => k s₂ ?_
    have u := u₁.twice u₂
    rwa [u₁.gpr, ofNat_2047_add (by omega)] at u

/-- `ld t, off(n)` (`ldAt`), at `a`. -/
theorem wp_ldAt {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4095)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hal : a.toNat % 8 = 0)
    (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Upd s s' t (s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (ldAt t n off ++ is)) s Q := by
  unfold ldAt
  split
  · exact wp_ld (by omega) ha hal hin k
  · refine wp_addi (imm := 2047) (by decide) fun s₁ u₁ => ?_
    refine wp_ld (by omega) (by rw [u₁.gpr, add_2047_add _ (by omega), ha]) hal
      (by rw [u₁.rd, u₁.wr]; exact hin) fun s₂ u₂ => k s₂ ?_
    rw [u₁.mem] at u₂
    exact u₁.twice u₂

/-- `sd t, off(n)` (`sdAt`), at `a`, for `t` another register than `n`. -/
theorem wp_sdAt {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4095) (htn : t ≠ n)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hal : a.toNat % 8 = 0) (hout : InRegions s.wr a 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (sdAt t n off ++ is)) s Q := by
  unfold sdAt
  split
  · exact wp_sd (by omega) ha hal hout k
  · refine wp_addi (imm := 2047) (by decide) fun s₁ u₁ => ?_
    refine wp_sd (by omega) (by rw [u₁.gpr, add_2047_add _ (by omega), ha]) hal
      (by rw [u₁.wr]; exact hout) fun s₂ u₂ => ?_
    refine wp_subi (imm := 2047) (by decide) fun s₃ u₃ => k s₃ ⟨funext fun r => ?_, ?_, ?_, ?_, ?_⟩
    · by_cases hr : r = n
      · subst hr; rw [u₃.gpr, u₂.gpr, u₁.gpr, BitVec.add_sub_cancel]
      · rw [u₃.other r hr, u₂.gpr, u₁.other r hr]
    · rw [u₃.mem, u₂.mem, u₁.other t htn, u₁.mem]
    · rw [u₃.rd, u₂.rd, u₁.rd]
    · rw [u₃.wr, u₂.wr, u₁.wr]
    · rw [u₃.sp, u₂.sp, u₁.sp]

end At

/-- A number of the working space, as the contracts read it. -/
theorem toNat_lo {o : Nat} (ho : o < 2 ^ 32) : ((BitVec.ofNat 64 o).setWidth 32).toNat = o := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide)]
  exact Nat.mod_eq_of_lt ho

theorem numAt_ofNat (m : Mem) (base : Addr) {o : Nat} (ho : o < 2 ^ 32) (k : Nat) :
    numAt m base ((BitVec.ofNat 64 o).setWidth 32) k = wordsVal m base o k := by
  rw [numAt, ← read_eq_wordsVal, toNat_lo ho]

/-- `Keeps` of the working space, and nothing written outside it, as `Outs`. -/
theorem outs_of_keeps {k : Nat} {base : Addr} {o : Nat} (ho : o < 2 ^ 32)
    {m m' : Mem} (hk : Keeps k base ((BitVec.ofNat 64 o).setWidth 32) m m')
    (hf : Frame [⟨base, 8192⟩] m m') (hk4 : 64 * k ≤ 4096) :
    Outs base [(o, 8 * k), (own k, 64 * k)] m m' := by
  intro x hx
  have h1 := hx _ (List.mem_cons_self ..)
  have h2 := hx _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  simp only [own, ownAt, ownBytes] at h1 h2
  by_cases hi : ofs base x < 8192
  · have e : x = base + BitVec.ofNat 64 (ofs base x) := by
      simp only [ofs, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rw [BitVec.add_comm, BitVec.sub_add_cancel]
    rw [e]
    refine hk _ hi ?_ ?_
    · simp only [ownAt, ownBytes]; omega
    · rw [toNat_lo ho]; omega
  · refine hf x fun r hr => ?_
    rw [List.mem_singleton] at hr; subst hr
    show ¬ ((x - base).toNat + 1 ≤ 8192)
    simp only [ofs] at hi; omega

/-- A call of `body`, which meets the contract `K` by register, from the
working space in `s0` and the offsets `o`, `a`, `b`. -/
theorem callOp_ok {S : Modulus} {f : String} {body : Prog isa} (hn : body.noFrames = true)
    {K : Contract isa} (hK : Meets body K) {s : State} {base : Addr} (hw : WsReg s base)
    {o a b : Nat} (ho : o + 8 * S.k ≤ own S.k) (ha : a + 8 * S.k ≤ own S.k) (hb : b + 8 * S.k ≤ own S.k)
    (ho' : o < 4095) (ha' : a < 4095) (hb' : b < 4095)
    (hpre : ∀ t : State, rvPre S t → t.gpr .a0 = base → offArg t .a1 = (BitVec.ofNat 64 o).setWidth 32 →
      offArg t .a2 = (BitVec.ofNat 64 a).setWidth 32 → offArg t .a3 = (BitVec.ofNat 64 b).setWidth 32 →
      t.mem = s.mem → K.pre t)
    {Q : State → Prop}
    (hQ : ∀ s', Kp s s' → Frame [⟨base, 8192⟩] s.mem s'.mem →
      ∀ t : State, t.gpr .a0 = base → offArg t .a1 = (BitVec.ofNat 64 o).setWidth 32 →
        offArg t .a2 = (BitVec.ofNat 64 a).setWidth 32 → offArg t .a3 = (BitVec.ofNat 64 b).setWidth 32 →
        t.mem = s.mem → K.post t (s'.withRegions [] [⟨base, 8192⟩]) → Q s') :
    WP isa (callOp f body o a b) s Q := by
  have hk : 64 * S.k ≤ 4096 := by simp only [own, ownAt, ownBytes] at ho; omega
  rw [callOp, ← List.append_nil (liAt .a3 b)]
  refine WP.seq (wp_mv fun s₁ u₁ => wp_liAt ho' fun s₂ u₂ => wp_liAt ha' fun s₃ u₃ => wp_liAt hb' fun s₄ u₄ =>
    WP.block_nil ?_)
  have K₄ : Kp s s₄ := (Kp.of_upd u₁).trans ((Kp.of_upd u₂).trans ((Kp.of_upd u₃).trans (Kp.of_upd u₄)))
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have g0 : s₄.gpr .a0 = base := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hw.s0]
  have g1 : s₄.gpr .a1 = BitVec.ofNat 64 o := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  have g2 : s₄.gpr .a2 = BitVec.ofNat 64 a := by rw [u₄.other _ (by decide), u₃.gpr]
  have g3 : s₄.gpr .a3 = BitVec.ofNat 64 b := u₄.gpr
  have hcov : Covers [⟨base, 8192⟩] s₄.wr := Covers.of_mem fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [K₄.wr]; exact hw.wr
  let e := s₄.callEntry.withRegions [] [⟨base, 8192⟩]
  have e0 : e.gpr .a0 = base := by
    simp only [e, State.withRegions_gpr]; rw [State.callEntry_gpr _ (by decide), g0]
  have e1 : offArg e .a1 = (BitVec.ofNat 64 o).setWidth 32 := by
    simp only [e, offArg, State.withRegions_gpr]; rw [State.callEntry_gpr _ (by decide), g1]
  have e2 : offArg e .a2 = (BitVec.ofNat 64 a).setWidth 32 := by
    simp only [e, offArg, State.withRegions_gpr]; rw [State.callEntry_gpr _ (by decide), g2]
  have e3 : offArg e .a3 = (BitVec.ofNat 64 b).setWidth 32 := by
    simp only [e, offArg, State.withRegions_gpr]; rw [State.callEntry_gpr _ (by decide), g3]
  have em : e.mem = s.mem := by simp only [e, State.withRegions_mem, State.callEntry_mem, m₄]
  have fit : ∀ x, x + 8 * S.k ≤ own S.k → Impl.Weierstrass.Mont.Fits S.k ((BitVec.ofNat 64 x).setWidth 32) :=
    fun x hx => by
      simp only [Impl.Weierstrass.Mont.Fits]
      rw [toNat_lo (by simp only [own, ownAt, ownBytes] at hx; omega)]
      exact hx
  have hpe : rvPre S e := ⟨rfl, by simp only [e, State.withRegions_wr, e0], by rw [e0]; exact hw.nowrap,
    ⟨by rw [e1]; exact fit o ho, by rw [e2]; exact fit a ha, by rw [e3]; exact fit b hb⟩,
    by rw [e0]; exact hw.al⟩
  refine WP.call hK (rd := []) (wr := [⟨base, 8192⟩]) (hpre e hpe e0 e1 e2 e3 em) (Covers.right hcov) hcov
    (fun s' r' w' p' F G _ hp => ?_) hn
  have K' : Kp s s' := K₄.trans ⟨G, r', w', p'⟩
  exact hQ s' K' (by rw [← m₄]; exact F) e e0 e1 e2 e3 em hp

/-- `[o] = [a] [b] R⁻¹ mod m` by a call. -/
theorem mulCall_ok {F : Field} (hF : FieldOk F) {s : State} {base : Addr} (hw : WsReg s base) {o a b : Nat}
    (ho : o + 8 * F.S.k ≤ own F.S.k) (ha : a + 8 * F.S.k ≤ own F.S.k) (hb : b + 8 * F.S.k ≤ own F.S.k)
    (ho' : o < 4095) (ha' : a < 4095) (hb' : b < 4095)
    (hB : wordsVal s.mem base b F.S.k < F.S.m) :
    WP isa (mulCall F o a b) s fun s' => CallKeep F.S.k base o s s' ∧
      wordsVal s'.mem base o F.S.k < F.S.m ∧
      wordsVal s'.mem base o F.S.k * 2 ^ (64 * F.S.k) % F.S.m =
        wordsVal s.mem base a F.S.k * wordsVal s.mem base b F.S.k % F.S.m := by
  have hk : 64 * F.S.k ≤ 4096 := by simp only [own, ownAt, ownBytes] at ho; omega
  have h32 : ∀ x, x + 8 * F.S.k ≤ own F.S.k → x < 2 ^ 32 := fun x hx => by
    simp only [own, ownAt, ownBytes] at hx; omega
  refine callOp_ok (S := F.S) hF.nmul hF.mul hw ho ha hb ho' ha' hb'
    (fun t ht h0 h1 h2 h3 hm => ⟨ht, by simp only [arg]; rw [h3, h0, hm, numAt_ofNat _ _ (h32 b hb)]; exact hB⟩)
    fun s' K Fr t h0 h1 h2 h3 hm ⟨v1, v2, v3⟩ => ?_
  simp only [res, arg, State.withRegions_mem, h0, h1, h2, h3, hm, numAt_ofNat _ _ (h32 _ ho),
    numAt_ofNat _ _ (h32 _ ha), numAt_ofNat _ _ (h32 _ hb)] at v1 v2 v3
  exact ⟨⟨K, outs_of_keeps (h32 o ho) v3 Fr hk⟩, v1, v2⟩

/-- `[o] = [a] + [b] mod m` by a call. -/
theorem addCall_ok {F : Field} (hF : FieldOk F) {s : State} {base : Addr} (hw : WsReg s base) {o a b : Nat}
    (ho : o + 8 * F.S.k ≤ own F.S.k) (ha : a + 8 * F.S.k ≤ own F.S.k) (hb : b + 8 * F.S.k ≤ own F.S.k)
    (ho' : o < 4095) (ha' : a < 4095) (hb' : b < 4095)
    (hAB : wordsVal s.mem base a F.S.k + wordsVal s.mem base b F.S.k < 2 * F.S.m) :
    WP isa (addCall F o a b) s fun s' => CallKeep F.S.k base o s s' ∧
      wordsVal s'.mem base o F.S.k = (wordsVal s.mem base a F.S.k + wordsVal s.mem base b F.S.k) % F.S.m := by
  have hk : 64 * F.S.k ≤ 4096 := by simp only [own, ownAt, ownBytes] at ho; omega
  have h32 : ∀ x, x + 8 * F.S.k ≤ own F.S.k → x < 2 ^ 32 := fun x hx => by
    simp only [own, ownAt, ownBytes] at hx; omega
  refine callOp_ok (S := F.S) hF.nadd hF.add hw ho ha hb ho' ha' hb'
    (fun t ht h0 h1 h2 h3 hm => ⟨ht, by
      simp only [arg]; rw [h2, h3, h0, hm, numAt_ofNat _ _ (h32 a ha), numAt_ofNat _ _ (h32 b hb)]; exact hAB⟩)
    fun s' K Fr t h0 h1 h2 h3 hm ⟨v1, v3⟩ => ?_
  simp only [res, arg, State.withRegions_mem, h0, h1, h2, h3, hm, numAt_ofNat _ _ (h32 _ ho),
    numAt_ofNat _ _ (h32 _ ha), numAt_ofNat _ _ (h32 _ hb)] at v1 v3
  exact ⟨⟨K, outs_of_keeps (h32 o ho) v3 Fr hk⟩, v1⟩

/-- `[o] = [a] - [b] mod m` by a call. -/
theorem subCall_ok {F : Field} (hF : FieldOk F) {s : State} {base : Addr} (hw : WsReg s base) {o a b : Nat}
    (ho : o + 8 * F.S.k ≤ own F.S.k) (ha : a + 8 * F.S.k ≤ own F.S.k) (hb : b + 8 * F.S.k ≤ own F.S.k)
    (ho' : o < 4095) (ha' : a < 4095) (hb' : b < 4095)
    (hA : wordsVal s.mem base a F.S.k < F.S.m) (hB : wordsVal s.mem base b F.S.k < F.S.m) :
    WP isa (subCall F o a b) s fun s' => CallKeep F.S.k base o s s' ∧
      wordsVal s'.mem base o F.S.k = (wordsVal s.mem base a F.S.k + F.S.m - wordsVal s.mem base b F.S.k) % F.S.m := by
  have hk : 64 * F.S.k ≤ 4096 := by simp only [own, ownAt, ownBytes] at ho; omega
  have h32 : ∀ x, x + 8 * F.S.k ≤ own F.S.k → x < 2 ^ 32 := fun x hx => by
    simp only [own, ownAt, ownBytes] at hx; omega
  refine callOp_ok (S := F.S) hF.nsub hF.sub hw ho ha hb ho' ha' hb'
    (fun t ht h0 h1 h2 h3 hm => ⟨ht, by simp only [arg]; rw [h2, h0, hm, numAt_ofNat _ _ (h32 a ha)]; exact hA,
      by simp only [arg]; rw [h3, h0, hm, numAt_ofNat _ _ (h32 b hb)]; exact hB⟩)
    fun s' K Fr t h0 h1 h2 h3 hm ⟨v1, v3⟩ => ?_
  simp only [res, arg, State.withRegions_mem, h0, h1, h2, h3, hm, numAt_ofNat _ _ (h32 _ ho),
    numAt_ofNat _ _ (h32 _ ha), numAt_ofNat _ _ (h32 _ hb)] at v1 v3
  exact ⟨⟨K, outs_of_keeps (h32 o ho) v3 Fr hk⟩, v1⟩

end VG.Proof.Weierstrass.RISCV64

namespace VG.Proof.Weierstrass.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps

/-- A call of `body`, which meets the contract `K` by register, on the
working space in `s0` (`a0 = s0`, then the call). -/
theorem wsCall_ok {f : String} {body : Prog isa} (hn : body.noFrames = true) {K : Contract isa}
    (hK : Meets body K) {s : State} {base : Addr} (hw : WsReg s base)
    (hpre : ∀ t : State, t.rd = [] → t.wr = [⟨base, 8192⟩] → t.gpr .a0 = base → t.mem = s.mem → K.pre t)
    {Q : State → Prop}
    (hQ : ∀ s', Kp s s' → ∀ t : State, t.gpr .a0 = base → t.mem = s.mem →
      K.post t (s'.withRegions [] [⟨base, 8192⟩]) → Q s') :
    WP isa (.seq (.block [.addi .a0 .s0 0]) (.call f body)) s Q := by
  refine WP.seq (wp_mv fun s₁ u₁ => WP.block_nil ?_)
  have K₁ : Kp s s₁ := Kp.of_upd u₁
  have hcov : Covers [⟨base, 8192⟩] s₁.wr := Covers.of_mem fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [K₁.wr]; exact hw.wr
  let e := s₁.callEntry.withRegions [] [⟨base, 8192⟩]
  have e0 : e.gpr .a0 = base := by
    simp only [e, State.withRegions_gpr]; rw [State.callEntry_gpr _ (by decide), u₁.gpr, hw.s0]
  have em : e.mem = s.mem := by simp only [e, State.withRegions_mem, State.callEntry_mem, u₁.mem]
  refine WP.call hK (rd := []) (wr := [⟨base, 8192⟩]) (hpre e rfl (by simp only [e, State.withRegions_wr]) e0 em)
    (Covers.right hcov) hcov (fun s' r' w' p' _ G _ hp => hQ s' (K₁.trans ⟨G, r', w', p'⟩) e e0 em hp) hn

end VG.Proof.Weierstrass.RISCV64

import VerifiedGarbage.Impl.Ed25519.X86_64.CombZmm
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Sym
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The `zmm` comb: each half of the `zmm` code is the `ymm` code

`tzs t is` runs the `ymm` block `is` on both 256-bit halves of the `zmm`
registers at once (`Impl/Ed25519/X86_64/CombZmm.lean`). Half `h` of a state
`z` is the state `half b h z` whose `ymm` registers are the halves `h` of
`z`'s `zmm` registers, and whose memory, in the window `[1024, 1792)` of the
scratch at `b`, is the half `h` of each 64-byte row at `zrow` (`hmem`).

`Rel b h J z y` says that `y` is half `h` of `z` but for the registers in
`J` (those a blend's free register has clobbered and the block has not
written since) and the rows of the `zmm` code (which `y` does not see).
`sim_wp`: if the `ymm` block, run from states related to the halves, ends
in `Q h`, the `zmm` block ends in a state whose halves are related to states
satisfying `Q h`. The check `junk` (by `decide`) says the block reads no
register of `J`, and what `J` is after it.
-/

namespace VG.Proof.Ed25519.X86_64.Zmm

open VG VG.X86_64 VG.Impl.Ed25519.X86_64.Zmm
open VG.Impl.X25519.X86_64 (sc)
open VG.Impl.X25519.X86_64.Ifma (y lanes)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi xi_inj)
open VG.Proof.X25519.X86_64.Ifma (rdiOff rdiOff_ok vm vm_vop)

/-! ## Halves -/

/-- The byte of half `h` of the `zmm` rows for offset `o` of the window. -/
def zoff (h o : Nat) : Nat := ZB + 64 * ((o - 1024) / 32) + 32 * h + (o - 1024) % 32

/-- Whether offset `o` is in the window `[1024, 1792)`. -/
def InWin (o : Nat) : Prop := 1024 ≤ o ∧ o < 1792

instance (o : Nat) : Decidable (InWin o) := by unfold InWin; infer_instance

/-- Whether offset `o` is in the rows of the window, `[ZB, ZMASK)`. -/
def InZ (o : Nat) : Prop := ZB ≤ o ∧ o < ZMASK

instance (o : Nat) : Decidable (InZ o) := by unfold InZ; infer_instance

/-- The memory half `h` sees: the window from the `zmm` rows. -/
def hmem (b : Addr) (h : Nat) (m : Mem) : Mem := fun a =>
  if InWin (a - b).toNat then m (b + BitVec.ofNat 64 (zoff h (a - b).toNat)) else m a

/-- Half `h` of a state. -/
def half (b : Addr) (h : Nat) (z : State) : State :=
  { z with
    xmm := fun r => z.zlane r (2 * h)
    ymmHi := fun r => z.zlane r (2 * h + 1)
    mem := hmem b h z.mem }

/-- `y` is half `h` of `z` but for the registers of `J` and the rows of the window. -/
structure Rel (b : Addr) (h : Nat) (J : List Nat) (z y : State) : Prop where
  xmm : ∀ r, xi r ∉ J → y.xmm r = z.zlane r (2 * h)
  hi : ∀ r, xi r ∉ J → y.ymmHi r = z.zlane r (2 * h + 1)
  gpr : y.gpr = z.gpr
  rd : y.rd = z.rd
  wr : y.wr = z.wr
  mem : ∀ a, ¬ InZ (a - b).toNat → y.mem a = hmem b h z.mem a

theorem Rel.half (b : Addr) (h : Nat) (J : List Nat) (z : State) : Rel b h J z (half b h z) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem Rel.lane {b : Addr} {h : Nat} {J : List Nat} {z y : State} (hr : Rel b h J z y) {r : XReg}
    (hj : xi r ∉ J) {k : Nat} (hk : k < 2) : y.lane r k = z.zlane r (2 * h + k) := by
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · exact hr.xmm r hj
  · exact hr.hi r hj

/-- The dword masks of a `vpblendd` selector's four bits. -/
def maskLane (n : BitVec 4) : BitVec 128 :=
  let f (k : Nat) : BitVec 32 := if n.getLsbD k then BitVec.allOnes 32 else 0
  ofDwords (f 0) (f 1) (f 2) (f 3)

/-- The `zmm` code's working space: the scratch at `b` (in `rdi`), with the masks of the
blends' selectors at `maskRow`. -/
structure ZOK (b : Addr) (z : State) : Prop where
  rdi : z.gpr .rdi = b
  wr : (⟨b, 8192⟩ : Region) ∈ z.wr
  nowrap : b.toNat + 8192 ≤ 2 ^ 64
  masks : ∀ sel ∈ blendSels, ∀ i < 4,
    (z.mem.readW (b + BitVec.ofNat 64 (maskRow sel)) 512).extractLsb' (128 * i) 128 =
      maskLane (sel.extractLsb' (4 * (i % 2)) 4)

/-! ## Lanes -/

theorem ternlog_AC (n : BitVec 4) (a c : BitVec 128) :
    ternlog (maskLane n) a c 0xAC = blendDwords a c n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  obtain ⟨q, s, rfl, hq, hs⟩ : ∃ q s, i = 32 * q + s ∧ q < 4 ∧ s < 32 :=
    ⟨i / 32, i % 32, by omega, by omega, by omega⟩
  simp only [ternlog, List.range, List.range.loop, List.foldl, BitVec.reduceGetLsb, Bool.false_eq_true,
    ↓reduceIte]
  simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.reducePow, Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff,
    decide_true, decide_false, ↓reduceIte, Bool.false_eq_true]
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and,
    BitVec.ofNat_eq_ofNat, BitVec.getLsbD_zero, Bool.false_or]
  simp only [maskLane, blendDwords, getLsbD_ofDwords_block _ _ _ _ hq hs]
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl <;>
    simp only [↓reduceIte, Nat.reduceEqDiff] <;>
    cases n.getLsbD _ <;>
    simp only [Bool.false_eq_true, ↓reduceIte, getLsbD_dword, decide_eq_true hs, Bool.true_and,
      BitVec.getLsbD_allOnes, Nat.mul_zero, Nat.zero_add] <;>
    cases a.getLsbD _ <;> cases c.getLsbD _ <;> simp

theorem zlane_vpternlogd (d a c : XReg) (n : BitVec 8) (s : State) (r : XReg) {i : Nat} (hi : i < 4) :
    ((ZOp.vpternlogd d a c n).exec s).zlane r i =
      if r = d then ternlog (s.zlane d i) (s.zlane a i) (s.zlane c i) n else s.zlane r i := by
  simp only [ZOp.exec]
  rw [State.zlane_setZ _ _ _ _ _ _ _ hi,
    pick4_lanes (fun i => ternlog (s.zlane d i) (s.zlane a i) (s.zlane c i) n) hi]

theorem zlane_vpmadd52 (hb : Bool) (d a c : XReg) (s : State) (r : XReg) {i : Nat} (hi : i < 4) :
    ((ZOp.vpmadd52 hb d a c).exec s).zlane r i =
      if r = d then madd52 hb (s.zlane d i) (s.zlane a i) (s.zlane c i) else s.zlane r i := by
  simp only [ZOp.exec]
  rw [State.zlane_setZ _ _ _ _ _ _ _ hi,
    pick4_lanes (fun i => madd52 hb (s.zlane d i) (s.zlane a i) (s.zlane c i)) hi]

theorem zlane_vpermq (d a : XReg) (o : BitVec 8) (s : State) (r : XReg) {h k : Nat} (hh : h < 2)
    (hk : k < 2) :
    ((ZOp.vpermq d a o).exec s).zlane r (2 * h + k) =
      if r = d then (permQwords (s.zlane a (2 * h + 1) ++ s.zlane a (2 * h)) o).extractLsb' (128 * k) 128
      else s.zlane r (2 * h + k) := by
  simp only [ZOp.exec]
  rw [State.zlane_setZ _ _ _ _ _ _ _ (by omega)]
  split
  · rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;> rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> rfl
  · rfl

theorem zlane_load (d : XReg) (v : BitVec 512) (s : State) (r : XReg) {i : Nat} (hi : i < 4) :
    (s.setZ d (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128)
      (v.extractLsb' 384 128)).zlane r i = if r = d then v.extractLsb' (128 * i) 128 else s.zlane r i := by
  rw [State.zlane_setZ _ _ _ _ _ _ _ hi, pick4_lanes (fun i => v.extractLsb' (128 * i) 128) hi]

/-- Half `h` of a `zmm` register. -/
theorem zmm_half (s : State) (r : XReg) {h : Nat} (hh : h < 2) :
    (s.zmm r).extractLsb' (256 * h) 256 = s.zlane r (2 * h + 1) ++ s.zlane r (2 * h) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [State.zmm, State.ymm, State.zlane, State.lane, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    decide_eq_true hj, Bool.true_and]
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
  · simp only [Nat.mul_zero, Nat.zero_add, show (0 : Nat) < 2 by decide, show (1 : Nat) < 2 by decide,
      show (1 : Nat) ≠ 0 by decide, ite_true, ite_false]
    rw [ite_eq_left hj]
  · simp only [show ¬ 256 * 1 + j < 256 by omega, ite_false, show ¬ (2 * 1 + 1 : Nat) < 2 by decide,
      show ¬ (2 * 1 : Nat) < 2 by decide, BitVec.getLsbD_extractLsb', show 256 * 1 + j - 256 = j by omega]
    by_cases h : j < 128
    · rw [ite_eq_left h, show 2 * 1 - 2 = 0 by rfl, Nat.mul_zero, Nat.zero_add, decide_eq_true h, Bool.true_and]
    · rw [ite_eq_right h, show 2 * 1 + 1 - 2 = 1 by rfl, Nat.mul_one, decide_eq_true (show j - 128 < 128 by omega),
        Bool.true_and, show 128 + (j - 128) = j by omega]

theorem ymm_lanes (s : State) (r : XReg) : s.ymm r = s.lane r 1 ++ s.lane r 0 := rfl

/-- `(x - (b + c)).toNat`, from `(x - b).toNat`. -/
theorem sub_off (x b : Addr) (c : Nat) :
    (x - (b + BitVec.ofNat 64 c)).toNat = (2 ^ 64 - c % 2 ^ 64 + (x - b).toNat) % 2 ^ 64 := by
  rw [Offset.sub_add_eq, Offset.toNat_sub_ofNat]

theorem off_ofNat (b : Addr) {x : Nat} (hx : x < 2 ^ 64) : (b + BitVec.ofNat 64 x - b).toNat = x :=
  Mem.sub_ofNat_toNat b hx

theorem eq_off (a b : Addr) : a = b + BitVec.ofNat 64 (a - b).toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

/-! ## The check: which registers a block leaves junk -/

/-- The `VBinOp`s `toZ` translates. -/
def zbinOk : VBinOp → Bool
  | .vpaddq | .vpsubq | .vpand | .vpor | .vpxor | .vpunpcklqdq | .vpunpckhqdq => true
  | _ => false

theorem zbin_sse {op : VBinOp} (h : zbinOk op = true) : (zbin op).sse = op.sse := by
  cases op <;> first | rfl | (simp [zbinOk] at h)

/-- A row of the window: `[rdi + o]`, `o` 32-byte aligned in `[1024, 1792)`. -/
def rowOk (m : MemOp) : Bool :=
  match rdiOff m with
  | some o => decide (1024 ≤ o ∧ o + 32 ≤ 1792 ∧ (o - 1024) % 32 = 0)
  | none => false

/-- `J` once `d` is written. -/
def jw (J : List Nat) (d : XReg) : List Nat := J.filter (· ≠ xi d)

/-- Whether `r` is not junk. -/
def free (J : List Nat) (r : XReg) : Bool := !(J.contains (xi r))

theorem free_iff {J : List Nat} {r : XReg} : free J r = true ↔ xi r ∉ J := by
  simp [free]

theorem not_mem_jw {J : List Nat} {d r : XReg} (h : xi r ∉ jw J d) (hd : r ≠ d) : xi r ∉ J := by
  intro hm; exact h (List.mem_filter.2 ⟨hm, by simpa [xi_inj] using hd⟩)

/-- The junk after one instruction, if it reads none. -/
def jstep (t : Nat) (J : List Nat) : Instr → Option (List Nat)
  | .vop (.vbin op .l256 d a c) => if zbinOk op && free J a && free J c then some (jw J d) else none
  | .vop (.vshift .psllq .l256 d a _) => if free J a then some (jw J d) else none
  | .vop (.vshift .psrlq .l256 d a _) => if free J a then some (jw J d) else none
  | .vop (.vpermq d a _) => if free J a then some (jw J d) else none
  | .vop (.vpmadd52luq .l256 d a c) =>
    if free J d && free J a && free J c then some (jw J d) else none
  | .vop (.vpmadd52huq .l256 d a c) =>
    if free J d && free J a && free J c then some (jw J d) else none
  | .vop (.vmovdqa .l256 d a) => if free J a then some (jw J d) else none
  | .vop (.vpblendd .l256 d a c sel) =>
    if free J a && free J c && decide (t < 16) && xi a != t && xi c != t && blendSels.contains sel then
      some (if xi d = t then jw J d else t :: jw J d) else none
  | .vop (.vperm2i128 d a c sel) =>
    if (sel == 0x20 || sel == 0x31) && free J a && free J c then some (jw J d) else none
  | .vmovdquLoad .l256 d m => if rowOk m then some (jw J d) else none
  | .vmovdquStore .l256 m r => if rowOk m && free J r then some J else none
  | _ => none

/-- The junk after a block, if it reads none. -/
def junk (t : Nat) : List Nat → List Instr → Option (List Nat)
  | J, [] => some J
  | J, i :: is => (jstep t J i).bind fun J' => junk t J' is

/-! ## One instruction -/

/-- What the `zmm` code keeps: all but the vector registers, and the memory but the rows of the
window. -/
structure ZKeep (b : Addr) (z z' : State) : Prop where
  vm : vm z z' = z'
  mem : ∀ a, ¬ InZ (a - b).toNat → z'.mem a = z.mem a

theorem vm_trans {a b c : State} (h₁ : vm a b = b) (h₂ : vm b c = c) : vm a c = c := by
  rw [← h₂, ← h₁]; rfl

theorem vm_gpr' {s s' : State} (h : vm s s' = s') : s'.gpr = s.gpr := by rw [← h]; rfl
theorem vm_rd' {s s' : State} (h : vm s s' = s') : s'.rd = s.rd := by rw [← h]; rfl
theorem vm_wr' {s s' : State} (h : vm s s' = s') : s'.wr = s.wr := by rw [← h]; rfl

theorem ZKeep.refl (b : Addr) (z : State) : ZKeep b z z := ⟨by cases z; rfl, fun _ _ => rfl⟩

theorem ZKeep.trans {b : Addr} {z₁ z₂ z₃ : State} (h₁ : ZKeep b z₁ z₂) (h₂ : ZKeep b z₂ z₃) :
    ZKeep b z₁ z₃ :=
  ⟨vm_trans h₁.vm h₂.vm, fun a ha => (h₂.mem a ha).trans (h₁.mem a ha)⟩

theorem ZOK.of_keep {b : Addr} {z z' : State} (hz : ZOK b z) (hk : ZKeep b z z') : ZOK b z' where
  rdi := by rw [vm_gpr' hk.vm]; exact hz.rdi
  wr := by rw [vm_wr' hk.vm]; exact hz.wr
  nowrap := hz.nowrap
  masks sel hs i hi := by
    rw [← hz.masks sel hs i hi]
    refine congrArg (fun (v : BitVec 512) => v.extractLsb' (128 * i) 128) ?_
    refine Mem.readW_congr fun j hj => hk.mem _ ?_
    have hm : ∀ sel ∈ blendSels, ZMASK ≤ maskRow sel ∧ maskRow sel + 64 ≤ 6016 := by decide
    have := hm sel hs
    rw [Offset.add_ofNat_add_ofNat, off_ofNat _ (by omega)]
    simp only [InZ]; omega

theorem ea_sc' {z : State} {b : Addr} (h : z.gpr .rdi = b) (d : Nat) : z.ea (sc d) = b + BitVec.ofNat 64 d := by
  simp only [State.ea, sc, VG.Impl.X25519.X86_64.at_, BitVec.ofInt_natCast, h]

theorem runBlock_one {i : Instr} {z z' : State} (h : exec i z = some z') : runBlock isa [i] z = some z' := by
  rw [runBlock_cons, h, runStep_some, runBlock_nil]

theorem runBlock_two {i j : Instr} {z z₁ z₂ : State} (h₁ : exec i z = some z₁) (h₂ : exec j z₁ = some z₂) :
    runBlock isa [i, j] z = some z₂ := by
  rw [runBlock_cons, h₁, runStep_some, runBlock_one h₂]

theorem runBlock_three {i j k : Instr} {z z₁ z₂ z₃ : State} (h₁ : exec i z = some z₁)
    (h₂ : exec j z₁ = some z₂) (h₃ : exec k z₂ = some z₃) : runBlock isa [i, j, k] z = some z₃ := by
  rw [runBlock_cons, h₁, runStep_some, runBlock_two h₂ h₃]

theorem zop_keep (b : Addr) (o : ZOp) (z : State) : ZKeep b z (o.exec z) :=
  ⟨by cases o <;> rfl, fun _ _ => by rw [ZOp.exec_mem]⟩

/-- A `ymm` result `lo, hi` to `d`, and the same to half `h` of `zmm d`: the halves stay related,
but for the registers of `J'`. -/
theorem rel_write {b : Addr} {h : Nat} {J J' : List Nat} {z y z' : State} (hr : Rel b h J z y)
    (hk : ZKeep b z z') (hm : z'.mem = z.mem) {d : XReg} {lo hi : BitVec 128}
    (hJ : ∀ r, xi r ∉ J' → r ≠ d → xi r ∉ J)
    (hl : ∀ r, r ≠ d → xi r ∉ J' → ∀ k < 2, z'.zlane r (2 * h + k) = z.zlane r (2 * h + k))
    (h0 : z'.zlane d (2 * h) = lo) (h1 : z'.zlane d (2 * h + 1) = hi) :
    Rel b h J' z' (y.setV .l256 d lo hi) where
  xmm r hj := by
    simp only [State.setV]
    split
    next e => rw [e]; exact h0.symm
    next hrd =>
      have e := hl r hrd hj 0 (by decide)
      rw [Nat.add_zero] at e
      rw [hr.xmm r (hJ r hj hrd), e]
  hi r hj := by
    simp only [State.setV]
    split
    next e => rw [e]; exact h1.symm
    next hrd => rw [hr.hi r (hJ r hj hrd), hl r hrd hj 1 (by decide)]
  gpr := by rw [vm_gpr' hk.vm]; exact hr.gpr
  rd := by rw [vm_rd' hk.vm]; exact hr.rd
  wr := by rw [vm_wr' hk.vm]; exact hr.wr
  mem a ha := by rw [hm]; exact hr.mem a ha

theorem jw_J {J : List Nat} {d : XReg} : ∀ r, xi r ∉ jw J d → r ≠ d → xi r ∉ J :=
  fun _ h hd => not_mem_jw h hd

/-- A lane-wise `zmm` operation and its `ymm` one. -/
theorem sim_lanewise {b : Addr} {J : List Nat} {d : XReg} {z : State} {o : ZOp} {v : VOp}
    {F : (XReg → Nat → BitVec 128) → Nat → BitVec 128}
    (hz : ∀ r i, i < 4 → (o.exec z).zlane r i = if r = d then F z.zlane i else z.zlane r i)
    (hv : ∀ y : State, v.exec y = y.setV .l256 d (F (fun r k => y.lane r k) 0) (F (fun r k => y.lane r k) 1))
    (hF : ∀ h < 2, ∀ y, Rel b h J z y → ∀ k < 2, F (fun r k => y.lane r k) k = F z.zlane (2 * h + k)) :
    ∀ h < 2, ∀ y y', Rel b h J z y → exec (.vop v) y = some y' → Rel b h (jw J d) (o.exec z) y' := by
  intro h hh y y' hr e
  simp only [exec, Option.some.injEq] at e
  subst e
  rw [hv]
  refine rel_write hr (zop_keep b o z) (ZOp.exec_mem o z) jw_J (fun r hrd _ k hk => ?_)
    ?_ ?_
  · rw [hz r _ (by omega), ite_eq_right hrd]
  · have e := hF h hh y hr 0 (by decide)
    rw [Nat.add_zero] at e
    rw [hz d _ (by omega), ite_eq_left rfl, e]
  · rw [hz d _ (by omega), ite_eq_left rfl, hF h hh y hr 1 (by decide)]

/-! ## Rows of the window -/

/-- A row of the window, at its offset. -/
def RowAt (o : Nat) : Prop := 1024 ≤ o ∧ o + 32 ≤ 1792 ∧ (o - 1024) % 32 = 0

instance (o : Nat) : Decidable (RowAt o) := by unfold RowAt; infer_instance

theorem rowOk_iff {m : MemOp} (h : rowOk m = true) : ∃ o, rdiOff m = some o ∧ RowAt o := by
  unfold rowOk at h
  split at h
  · rename_i o ho; exact ⟨o, ho, of_decide_eq_true h⟩
  · cases h

theorem zmem_ea {m : MemOp} {o : Nat} (h : rdiOff m = some o) (ho : 1024 ≤ o) (s : State) :
    s.ea (zmem m) = s.gpr .rdi + BitVec.ofNat 64 (zrow o) := by
  unfold rdiOff at h
  split at h
  · rename_i hb
    split at h
    · rename_i n hn
      cases h
      have e : ((ZB : Int) + 2 * (Int.ofNat o - 1024)) = ((zrow o : Nat) : Int) := by
        unfold zrow; rw [Int.ofNat_eq_natCast]; omega
      simp only [State.ea, zmem, hb.1, hb.2, hn, e, BitVec.ofInt_natCast]
    · cases h
  · cases h

/-- The bytes of a row as half `h` sees them. -/
theorem win_byte {b : Addr} {h : Nat} {J : List Nat} {z y : State} (hr : Rel b h J z y) {o : Nat}
    (ho : RowAt o) {j : Nat} (hj : j < 32) :
    y.mem (b + BitVec.ofNat 64 (o + j)) = z.mem (b + BitVec.ofNat 64 (zrow o + 32 * h + j)) := by
  obtain ⟨h1, h2, h3⟩ := ho
  rw [hr.mem _ (by rw [off_ofNat _ (by omega)]; unfold InZ ZB; omega), hmem,
    off_ofNat _ (by omega), ite_eq_left (by simp only [InWin]; omega)]
  refine congrArg z.mem (congrArg (b + ·) (congrArg (BitVec.ofNat 64) ?_))
  unfold zoff zrow
  omega

theorem read_congr2 {m m' : Mem} {a a' : Addr} {n : Nat}
    (h : ∀ i < n, m (a + BitVec.ofNat 64 i) = m' (a' + BitVec.ofNat 64 i)) :
    m.read a n = m'.read a' n := by
  induction n generalizing a a' with
  | zero => rfl
  | succ n ih =>
    simp only [Mem.read]
    have h0 := h 0 (by omega)
    simp only [BitVec.add_zero] at h0
    rw [h0, ih fun i hi => ?_]
    have := h (i + 1) (by omega)
    rwa [Offset.add_ofNat_succ, Offset.add_ofNat_succ] at this

theorem readW_congr2 {m m' : Mem} {a a' : Addr} {w : Nat}
    (h : ∀ i < w / 8, m (a + BitVec.ofNat 64 i) = m' (a' + BitVec.ofNat 64 i)) :
    m.readW a w = m'.readW a' w := by
  simp only [Mem.readW, read_congr2 h]

/-- A load of a row, as half `h` sees it. -/
theorem win_read {b : Addr} {h : Nat} {J : List Nat} {z y : State} (hr : Rel b h J z y) (hh : h < 2)
    {o : Nat} (ho : RowAt o) {k : Nat} (hk : k < 2) :
    (z.mem.readW (b + BitVec.ofNat 64 (zrow o)) 512).extractLsb' (128 * (2 * h + k)) 128 =
      (y.mem.readW (b + BitVec.ofNat 64 o) 256).extractLsb' (128 * k) 128 := by
  have e₁ := readW_extract z.mem (b + BitVec.ofNat 64 (zrow o)) (w := 512) (k := 16 * (2 * h + k))
    (n := 16) (by omega)
  have e₂ := readW_extract y.mem (b + BitVec.ofNat 64 o) (w := 256) (k := 16 * k) (n := 16) (by omega)
  rw [show 8 * (16 * (2 * h + k)) = 128 * (2 * h + k) by omega] at e₁
  rw [show 8 * (16 * k) = 128 * k by omega] at e₂
  rw [e₁, e₂]
  refine (readW_congr2 fun j hj => ?_).symm
  simp only [Offset.add_ofNat_add_ofNat]
  rw [Nat.add_assoc, win_byte hr ho (j := 16 * k + j) (by omega)]
  refine congrArg z.mem (congrArg (b + ·) (congrArg (BitVec.ofNat 64) ?_))
  omega

/-- Byte `j` of half `h` of a `zmm` register. -/
theorem zmm_byte (s : State) (r : XReg) {h j : Nat} (hh : h < 2) (hj : j < 32) :
    (s.zmm r).extractLsb' (8 * (32 * h + j)) 8 =
      (s.zlane r (2 * h + 1) ++ s.zlane r (2 * h)).extractLsb' (8 * j) 8 := by
  rw [← zmm_half s r hh]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    decide_eq_true (show 8 * j + i < 256 by omega)]
  congr 1; omega

/-- The bytes of a written row, as half `h` sees them. -/
theorem win_write {b : Addr} {h : Nat} {J : List Nat} {z y : State} (hr : Rel b h J z y) (hh : h < 2)
    {o : Nat} (ho : RowAt o) {r : XReg} (hf : xi r ∉ J) (a : Addr)
    (ha : ¬ InZ (a - b).toNat) :
    (y.mem.writeW (b + BitVec.ofNat 64 o) (y.ymm r)) a =
      hmem b h (z.mem.writeW (b + BitVec.ofNat 64 (zrow o)) (z.zmm r)) a := by
  obtain ⟨h1, h2, h3⟩ := ho
  have hx := (a - b).isLt
  simp only [Mem.writeW, Mem.write, hmem]
  rw [sub_off]
  generalize hxd : (a - b).toNat = x at *
  by_cases hin : o ≤ x ∧ x < o + 32
  · have hz : zrow o ≤ zoff h x ∧ zoff h x < zrow o + 64 := by
      unfold zoff zrow; omega
    rw [ite_eq_left (by omega), ite_eq_left (by simp only [InWin]; omega), Offset.add_sub_add_left,
      Offset.ofNat_sub_ofNat hz.1, BitVec.toNat_ofNat, ite_eq_left (by omega)]
    have e : (2 ^ 64 - o % 2 ^ 64 + x) % 2 ^ 64 = x - o := by omega
    have e' : (zoff h x - zrow o) % 2 ^ 64 = 32 * h + (x - o) := by
      unfold zoff zrow; omega
    rw [e, e']
    simp only [BitVec.setWidth_eq]
    rw [zmm_byte z r hh (by omega), State.ymm, ← hr.hi r hf, ← hr.xmm r hf]
  · rw [ite_eq_right (by omega), hr.mem a (hxd ▸ ha), hmem, hxd]
    split
    · rename_i hw
      rw [Offset.add_sub_add_left, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        ite_eq_right]
      simp only [InWin] at hw
      unfold zoff zrow
      omega
    · simp only [InZ] at ha
      rw [sub_off, ite_eq_right (by unfold zrow at *; unfold ZB ZMASK at *; omega)]

/-! ## Each instruction -/

theorem zrow_in {o : Nat} (ho : RowAt o) : ZB ≤ zrow o ∧ zrow o + 64 ≤ ZMASK := by
  obtain ⟨h1, h2, h3⟩ := ho; unfold zrow ZB ZMASK; omega

theorem scratch_in {b : Addr} {z : State} (hz : ZOK b z) {d : Nat} (hd : d + 64 ≤ 8192) :
    InRegions z.wr (b + BitVec.ofNat 64 d) 64 :=
  ⟨_, hz.wr, Offset.contains_base b hd (by omega)⟩

theorem setZ_keep (b : Addr) (z : State) (d : XReg) (l0 l1 l2 l3 : BitVec 128) :
    ZKeep b z (z.setZ d l0 l1 l2 l3) := ⟨rfl, fun _ _ => rfl⟩

/-- A load of a row. -/
theorem sim_load {b : Addr} {t : Nat} {J : List Nat} {d : XReg} {m : MemOp} (hm : rowOk m = true)
    {z : State} (hz : ZOK b z) :
    ∃ z', runBlock isa (toZ t (.vmovdquLoad .l256 d m)) z = some z' ∧ ZKeep b z z' ∧
      ∀ h < 2, ∀ y y', Rel b h J z y → exec (.vmovdquLoad .l256 d m) y = some y' →
        Rel b h (jw J d) z' y' := by
  obtain ⟨o, ho, hr⟩ := rowOk_iff hm
  have ea : z.ea (zmem m) = b + BitVec.ofNat 64 (zrow o) := by rw [zmem_ea ho hr.1, hz.rdi]
  have hin : InRegions (z.rd ++ z.wr) (b + BitVec.ofNat 64 (zrow o)) 64 := by
    obtain ⟨r, hr', hc⟩ := scratch_in hz (d := zrow o) (by have := zrow_in hr; unfold ZMASK at this; omega)
    exact ⟨r, List.mem_append_right _ hr', hc⟩
  let w := z.mem.readW (b + BitVec.ofNat 64 (zrow o)) 512
  refine ⟨z.setZ d (w.extractLsb' 0 128) (w.extractLsb' 128 128) (w.extractLsb' 256 128)
    (w.extractLsb' 384 128), runBlock_one ?_, setZ_keep b z d _ _ _ _, ?_⟩
  · simp only [exec, ea, State.load512, hin, ite_true, Option.map_some]; rfl
  intro h hh y y' hy e
  have eay : y.ea m = b + BitVec.ofNat 64 o := by rw [rdiOff_ok ho, hy.gpr, hz.rdi]
  simp only [exec, eay, State.load256] at e
  split at e
  case isFalse => cases e
  simp only [Option.map_some, Option.some.injEq] at e
  subst e
  have r0 := win_read hy hh hr (k := 0) (by decide)
  have r1 := win_read hy hh hr (k := 1) (by decide)
  rw [Nat.add_zero, Nat.mul_zero] at r0
  rw [Nat.mul_one] at r1
  refine rel_write hy (setZ_keep b z d _ _ _ _) rfl jw_J (fun r hrd _ k hk => ?_) ?_ ?_
  · rw [zlane_load _ _ _ _ (by omega), ite_eq_right hrd]
  · rw [zlane_load _ _ _ _ (by omega), ite_eq_left rfl]; exact r0
  · rw [zlane_load _ _ _ _ (by omega), ite_eq_left rfl]; exact r1

/-- A store of a row. -/
theorem sim_store {b : Addr} {t : Nat} {J : List Nat} {r : XReg} {m : MemOp} (hm : rowOk m = true)
    (hf : xi r ∉ J) {z : State} (hz : ZOK b z) :
    ∃ z', runBlock isa (toZ t (.vmovdquStore .l256 m r)) z = some z' ∧ ZKeep b z z' ∧
      ∀ h < 2, ∀ y y', Rel b h J z y → exec (.vmovdquStore .l256 m r) y = some y' → Rel b h J z' y' := by
  obtain ⟨o, ho, hr⟩ := rowOk_iff hm
  have ea : z.ea (zmem m) = b + BitVec.ofNat 64 (zrow o) := by rw [zmem_ea ho hr.1, hz.rdi]
  have zi := zrow_in hr
  have hin : InRegions z.wr (b + BitVec.ofNat 64 (zrow o)) 64 :=
    scratch_in hz (d := zrow o) (by unfold ZMASK at zi; omega)
  refine ⟨z.setMem (z.mem.writeW (b + BitVec.ofNat 64 (zrow o)) (z.zmm r)), runBlock_one ?_, ⟨rfl, ?_⟩, ?_⟩
  · simp only [exec, ea, State.store512_eq, hin, ite_true]
  · intro a ha
    simp only [State.setMem, Mem.writeW, Mem.write]
    rw [sub_off, ite_eq_right]
    have := (a - b).isLt
    unfold InZ at ha
    unfold ZB ZMASK at ha zi
    omega
  intro h hh y y' hy e
  have eay : y.ea m = b + BitVec.ofNat 64 o := by rw [rdiOff_ok ho, hy.gpr, hz.rdi]
  simp only [exec, eay, State.store256] at e
  split at e
  case isFalse => cases e
  simp only [Option.some.injEq] at e
  subst e
  exact ⟨fun r' hr' => by rw [hy.xmm r' hr']; rfl, fun r' hr' => by rw [hy.hi r' hr']; rfl, hy.gpr, hy.rd,
    hy.wr, fun a ha => win_write hy hh hr hf a ha⟩

theorem xi_y {t : Nat} (ht : t < 16) : xi (y t) = t := by
  have e : ∀ t < 16, xi (y t) = t := by decide
  exact e t ht

/-- A blend, through the free register `y t`. -/
theorem sim_blend {b : Addr} {t : Nat} {J : List Nat} {d a c : XReg} {sel : BitVec 8} (ht : t < 16)
    (ha : xi a ≠ t) (hc : xi c ≠ t) (hfa : xi a ∉ J) (hfc : xi c ∉ J) (hs : sel ∈ blendSels)
    {z : State} (hz : ZOK b z) :
    ∃ z', runBlock isa (toZ t (.vop (.vpblendd .l256 d a c sel))) z = some z' ∧ ZKeep b z z' ∧
      ∀ h < 2, ∀ y' y'', Rel b h J z y' → exec (.vop (.vpblendd .l256 d a c sel)) y' = some y'' →
        Rel b h (if xi d = t then jw J d else t :: jw J d) z' y'' := by
  have hT := xi_y ht
  have hm : ∀ sel ∈ blendSels, maskRow sel + 64 ≤ 8192 := by decide
  have hin : InRegions (z.rd ++ z.wr) (b + BitVec.ofNat 64 (maskRow sel)) 64 := by
    obtain ⟨r, hr', hc'⟩ := scratch_in hz (hm sel hs)
    exact ⟨r, List.mem_append_right _ hr', hc'⟩
  have haT : a ≠ y t := fun e => ha (by rw [e, hT])
  have hcT : c ≠ y t := fun e => hc (by rw [e, hT])
  let w := z.mem.readW (b + BitVec.ofNat 64 (maskRow sel)) 512
  let z₁ := z.setZ (y t) (w.extractLsb' 0 128) (w.extractLsb' 128 128) (w.extractLsb' 256 128)
    (w.extractLsb' 384 128)
  let z₂ := (ZOp.vpternlogd (y t) a c 0xAC).exec z₁
  let z₃ := (ZOp.vmovdqa64 d (y t)).exec z₂
  have L : ∀ r i, i < 4 → z₃.zlane r i =
      if r = d ∨ r = y t then blendDwords (z.zlane a i) (z.zlane c i) (sel.extractLsb' (4 * (i % 2)) 4)
      else z.zlane r i := by
    intro r i hi
    simp only [z₃, z₂, z₁, zlane_vmovdqa64 _ _ _ _ hi, zlane_vpternlogd _ _ _ _ _ _ hi, zlane_load _ _ _ _ hi,
      ite_true, haT, hcT, ite_false]
    rw [hz.masks sel hs i hi, ternlog_AC]
    by_cases h1 : r = d <;> by_cases h2 : r = y t <;> simp [h1, h2]
  refine ⟨z₃, runBlock_three ?_ rfl rfl,
    (setZ_keep b z _ _ _ _ _).trans ((zop_keep b _ _).trans (zop_keep b _ _)), ?_⟩
  · simp only [exec, ea_sc' hz.rdi, State.load512, hin, ite_true, Option.map_some]; rfl
  intro h hh y' y'' hy e
  simp only [exec, Option.some.injEq] at e
  subst e
  refine rel_write hy ((setZ_keep b z _ _ _ _ _).trans ((zop_keep b _ _).trans (zop_keep b _ _))) rfl
    (fun r hr hrd => ?_) (fun r hrd hr k hk => ?_) ?_ ?_
  · by_cases hd : xi d = t
    · rw [ite_eq_left hd] at hr; exact jw_J r hr hrd
    · rw [ite_eq_right hd] at hr; exact jw_J r (fun h' => hr (List.mem_cons_of_mem _ h')) hrd
  · have hrT : r ≠ y t := by
      intro e
      by_cases hd : xi d = t
      · exact hrd (xi_inj.1 (by rw [e, hT, hd]))
      · rw [ite_eq_right hd, e, hT] at hr; exact hr (List.mem_cons_self ..)
    rw [L r _ (by omega), ite_eq_right (fun h' => h'.elim hrd hrT)]
  · rw [L d _ (by omega), ite_eq_left (Or.inl rfl), hy.lane hfa (k := 0) (by decide),
      hy.lane hfc (k := 0) (by decide), Nat.add_zero]
    simp only [Nat.mul_mod_right, Nat.mul_zero]
  · rw [L d _ (by omega), ite_eq_left (Or.inl rfl), hy.lane hfa (k := 1) (by decide),
      hy.lane hfc (k := 1) (by decide)]
    simp only [show (2 * h + 1) % 2 = 1 by omega, Nat.mul_one]

theorem perm2Lanes_congr {a a' c c' : Nat → BitVec 128} (ha : ∀ k < 2, a k = a' k) (hc : ∀ k < 2, c k = c' k)
    (sel : BitVec 8) (j : Nat) : perm2Lanes a c sel j = perm2Lanes a' c' sel j := by
  simp only [perm2Lanes]
  rw [ha _ (Nat.mod_lt _ (by decide)), hc _ (Nat.mod_lt _ (by decide))]

/-- `vperm2i128` with `0x20` or `0x31`, as two `vshufi32x4`. -/
theorem sim_perm2 {b : Addr} {t : Nat} {J : List Nat} {d a c : XReg} {sel : BitVec 8}
    (hsel : sel = 0x20 ∨ sel = 0x31) (hfa : xi a ∉ J) (hfc : xi c ∉ J) (z : State) :
    ∃ z', runBlock isa (toZ t (.vop (.vperm2i128 d a c sel))) z = some z' ∧ ZKeep b z z' ∧
      ∀ h < 2, ∀ y' y'', Rel b h J z y' → exec (.vop (.vperm2i128 d a c sel)) y' = some y'' →
        Rel b h (jw J d) z' y'' := by
  have key : ∀ h < 2, ∀ k < 2, ((ZOp.vshufi32x4 d d d 0xD8).exec ((ZOp.vshufi32x4 d a c
      (if sel = 0x31 then 0xDD else 0x88)).exec z)).zlane d (2 * h + k) =
      perm2Lanes (fun k => z.zlane a (2 * h + k)) (fun k => z.zlane c (2 * h + k)) sel k := by
    intro h hh k hk
    rcases hsel with rfl | rfl <;> rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;>
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;>
      simp [zlane_vshufi32x4, shuf4Lanes, perm2Lanes]
  refine ⟨_, runBlock_two rfl rfl, (zop_keep b _ _).trans (zop_keep b _ _), ?_⟩
  intro h hh y' y'' hy e
  simp only [exec, Option.some.injEq] at e
  subst e
  have pc : ∀ k, perm2Lanes (y'.lane a) (y'.lane c) sel k =
      perm2Lanes (fun k => z.zlane a (2 * h + k)) (fun k => z.zlane c (2 * h + k)) sel k :=
    perm2Lanes_congr (fun k hk => hy.lane hfa hk) (fun k hk => hy.lane hfc hk) sel
  refine rel_write hy ((zop_keep b _ _).trans (zop_keep b _ _)) rfl jw_J (fun r hrd _ k hk => ?_) ?_ ?_
  · simp only [zlane_vshufi32x4 _ _ _ _ _ _ (show 2 * h + k < 4 by omega), hrd, ite_false]
  · rw [← Nat.add_zero (2 * h), key h hh 0 (by decide), pc]
  · rw [key h hh 1 (by decide), pc]

/-- One instruction of a translated block. -/
theorem sim1 {b : Addr} {t : Nat} {J J' : List Nat} {i : Instr} (hj : jstep t J i = some J') {z : State}
    (hz : ZOK b z) :
    ∃ z', runBlock isa (toZ t i) z = some z' ∧ ZKeep b z z' ∧
      ∀ h < 2, ∀ y y', Rel b h J z y → exec i y = some y' → Rel b h J' z' y' := by
  unfold jstep at hj
  split at hj
  next op d a c =>
    split at hj
    case isFalse => cases hj
    next hc =>
    cases hj
    simp only [Bool.and_eq_true, free_iff] at hc
    obtain ⟨⟨hop, ha⟩, hc⟩ := hc
    exact ⟨_, runBlock_one rfl, zop_keep b _ z, sim_lanewise (F := fun L i => op.sse.eval (L a i) (L c i))
      (fun r i hi => by rw [zlane_zbin _ _ _ _ _ _ hi, zbin_sse hop]) (fun _ => rfl)
      (fun h hh y hr k hk => by simp only; rw [hr.lane ha hk, hr.lane hc hk])⟩
  next d a n =>
    split at hj
    case isFalse => cases hj
    next ha =>
    cases hj
    rw [free_iff] at ha
    exact ⟨_, runBlock_one rfl, zop_keep b _ z, sim_lanewise (F := fun L i => XShiftOp.psllq.eval (L a i) n)
      (fun r i hi => by rw [zlane_vshift _ _ _ _ _ _ hi]; rfl) (fun _ => rfl)
      (fun h hh y hr k hk => by simp only; rw [hr.lane ha hk])⟩
  next d a n =>
    split at hj
    case isFalse => cases hj
    next ha =>
    cases hj
    rw [free_iff] at ha
    exact ⟨_, runBlock_one rfl, zop_keep b _ z, sim_lanewise (F := fun L i => XShiftOp.psrlq.eval (L a i) n)
      (fun r i hi => by rw [zlane_vshift _ _ _ _ _ _ hi]; rfl) (fun _ => rfl)
      (fun h hh y hr k hk => by simp only; rw [hr.lane ha hk])⟩
  next d a o =>
    split at hj
    case isFalse => cases hj
    next ha =>
    cases hj
    rw [free_iff] at ha
    refine ⟨_, runBlock_one rfl, zop_keep b _ z, sim_lanewise
      (F := fun L i => (permQwords (L a (2 * (i / 2) + 1) ++ L a (2 * (i / 2))) o).extractLsb' (128 * (i % 2)) 128)
      (fun r i hi => ?_) (fun _ => rfl) (fun h hh y hr k hk => ?_)⟩
    · have e := zlane_vpermq d a o z r (h := i / 2) (k := i % 2) (by omega) (by omega)
      rw [show 2 * (i / 2) + i % 2 = i by omega] at e
      exact e
    · simp only [show k / 2 = 0 by omega, show (2 * h + k) / 2 = h by omega, show (2 * h + k) % 2 = k by omega,
        show k % 2 = k by omega, Nat.mul_zero, Nat.zero_add]
      rw [hr.lane ha (k := 1) (by decide), show y.lane a 0 = z.zlane a (2 * h) from hr.xmm a ha]
  next d a c =>
    split at hj
    case isFalse => cases hj
    next hc =>
    cases hj
    simp only [Bool.and_eq_true, free_iff] at hc
    obtain ⟨⟨hd, ha⟩, hc⟩ := hc
    exact ⟨_, runBlock_one rfl, zop_keep b _ z,
      sim_lanewise (F := fun L i => madd52 false (L d i) (L a i) (L c i))
      (fun r i hi => by rw [zlane_vpmadd52 _ _ _ _ _ _ hi]) (fun _ => rfl)
      (fun h hh y hr k hk => by simp only; rw [hr.lane hd hk, hr.lane ha hk, hr.lane hc hk])⟩
  next d a c =>
    split at hj
    case isFalse => cases hj
    next hc =>
    cases hj
    simp only [Bool.and_eq_true, free_iff] at hc
    obtain ⟨⟨hd, ha⟩, hc⟩ := hc
    exact ⟨_, runBlock_one rfl, zop_keep b _ z,
      sim_lanewise (F := fun L i => madd52 true (L d i) (L a i) (L c i))
      (fun r i hi => by rw [zlane_vpmadd52 _ _ _ _ _ _ hi]) (fun _ => rfl)
      (fun h hh y hr k hk => by simp only; rw [hr.lane hd hk, hr.lane ha hk, hr.lane hc hk])⟩
  next d a =>
    split at hj
    case isFalse => cases hj
    next ha =>
    cases hj
    rw [free_iff] at ha
    exact ⟨_, runBlock_one rfl, zop_keep b _ z, sim_lanewise (F := fun L i => L a i)
      (fun r i hi => by rw [zlane_vmovdqa64 _ _ _ _ hi]) (fun _ => rfl)
      (fun h hh y hr k hk => by simp only; rw [hr.lane ha hk])⟩
  next d a c sel =>
    split at hj
    case isFalse => cases hj
    next hc =>
    cases hj
    simp only [Bool.and_eq_true, free_iff, decide_eq_true_eq, bne_iff_ne, ne_eq, List.contains_iff_mem]
      at hc
    obtain ⟨⟨⟨⟨⟨ha, hc'⟩, ht⟩, hat⟩, hct⟩, hs⟩ := hc
    exact sim_blend ht hat hct ha hc' hs hz
  next d a c sel =>
    split at hj
    case isFalse => cases hj
    next hc =>
    cases hj
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, free_iff] at hc
    obtain ⟨⟨hs, ha⟩, hc⟩ := hc
    exact sim_perm2 hs ha hc z
  next d m =>
    split at hj
    case isFalse => cases hj
    next hm =>
    cases hj
    exact sim_load hm hz
  next m r =>
    split at hj
    case isFalse => cases hj
    next hm =>
    cases hj
    simp only [Bool.and_eq_true, free_iff] at hm
    exact sim_store hm.1 hm.2 hz
  · cases hj

/-! ## Blocks -/

/-- A translated block: if the `ymm` block, from states related to the halves, ends in `Q h`,
the `zmm` block ends in a state whose halves are related to states satisfying `Q h`. -/
theorem sim_run {b : Addr} {t : Nat} : ∀ (is : List Instr) {J J' : List Nat}, junk t J is = some J' →
    ∀ {z : State}, ZOK b z → ∀ {Q : Nat → State → Prop},
      (∀ h < 2, ∃ y, Rel b h J z y ∧ WP isa (.block is) y (Q h)) →
      WP isa (.block (tzs t is)) z fun z' => ZOK b z' ∧ ZKeep b z z' ∧
        ∀ h < 2, ∃ y, Rel b h J' z' y ∧ Q h y
  | [], J, J', hj, z, hz, Q, hy => by
    simp only [junk, Option.some.injEq] at hj
    subst hj
    exact WP.block_nil ⟨hz, ZKeep.refl b z, fun h hh => by
      obtain ⟨y, hr, hw⟩ := hy h hh
      exact ⟨y, hr, WP.block_nil_iff.1 hw⟩⟩
  | i :: is, J, J', hj, z, hz, Q, hy => by
    simp only [junk, Option.bind_eq_some_iff] at hj
    obtain ⟨J₁, hj₁, hj₂⟩ := hj
    obtain ⟨z₁, hz₁, hk₁, hr₁⟩ := sim1 hj₁ hz
    rw [tzs, List.flatMap_cons, WP.block_append_iff]
    refine WP.of_runBlock ⟨z₁, hz₁, ?_⟩
    refine WP.mono (sim_run is hj₂ (hz.of_keep hk₁) fun h hh => ?_) fun z' ⟨o, k, r⟩ => ⟨o, hk₁.trans k, r⟩
    obtain ⟨y, hr, hw⟩ := hy h hh
    obtain ⟨y₁, e, hw₁⟩ := WP.block_cons_iff.1 hw
    exact ⟨y₁, hr₁ h hh y y₁ hr e, hw₁⟩

/-- `sim_run` from the halves themselves. -/
theorem sim_wp {b : Addr} {t : Nat} {is : List Instr} {J' : List Nat} (hj : junk t [] is = some J')
    {z : State} (hz : ZOK b z) {Q : Nat → State → Prop} (hy : ∀ h < 2, WP isa (.block is) (half b h z) (Q h)) :
    WP isa (.block (tzs t is)) z fun z' => ZOK b z' ∧ ZKeep b z z' ∧
      ∀ h < 2, ∃ y, Rel b h J' z' y ∧ Q h y :=
  sim_run is hj hz fun h hh => ⟨_, Rel.half b h [] z, hy h hh⟩

end VG.Proof.Ed25519.X86_64.Zmm

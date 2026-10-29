module

public import VerifiedGarbage.Impl.Rsa.Arm.KeyCheck
public import VerifiedGarbage.Proof.Rsa.Arm.KeyArrs
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The checks of an RSA key on ARMv7: the state between the steps

`Geo`: the working space (`B`, `Z` bytes) and the modulus' length `K`, which
two runs share; `Vals`: the numbers read, which they may not. `Stg g s₀ A
live c s`: from the state `s₀` the checks start from, the steps so far wrote
only the arrays and the header words they may, the arrays `live` hold `A`,
and the mask is `c`. `StgD`: the same after a division, which leaves only
`r8` of the working space's registers.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

structure Geo where
  B : BitVec 32
  Z : Nat
  K : Nat

/-- `w = ⌈K / 4⌉`. -/
abbrev Geo.w (g : Geo) : Nat := (g.K + 3) / 4

structure Vals where
  n : Nat
  e : Nat
  p : Nat
  q : Nat
  dP : Nat
  dQ : Nat
  qI : Nat
  d : Nat

/-- The arrays after the numbers are read (in the order the entry reads them). -/
def vals (v : Vals) : Nat → Nat :=
  upd (upd (upd (upd (upd (upd (upd (upd (fun _ => 0) aE v.e) aD v.d) aP v.p) aQ v.q) aDP v.dP) aDQ v.dQ)
    aQI v.qI) aN v.n

/-- The header words the checks write. -/
abbrev bodySlots : List Nat := [0, 4, 8, 12, sB, sC, sT, sF, sMask]

/-- The registers the checks may change: all but `r8`. -/
abbrev bodyRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r9, .r10, .r11, .r12, .lr]

/-- `Ws` but for `r7` and `r9`. -/
structure WsR (s : State) (B : BitVec 32) (Z w N : Nat) : Prop where
  nowrap : B.toNat + Z ≤ 2 ^ 32
  writable : (⟨State.addr B, Z⟩ : Region) ∈ s.wr
  fits : arr w N ≤ Z
  wpos : 0 < w
  wle : w ≤ 1024
  r8 : s.gpr .r8 = B

theorem Ws.toR {s : State} {B : BitVec 32} {Z w N : Nat} (h : Ws s B Z w N) : WsR s B Z w N :=
  ⟨h.nowrap, h.writable, h.fits, h.wpos, h.wle, h.r8⟩

theorem WsR.ws {s : State} {B : BitVec 32} {Z w N : Nat} (h : WsR s B Z w N)
    (h7 : s.gpr .r7 = BitVec.ofNat 32 (S w)) (h9 : s.gpr .r9 = BitVec.ofNat 32 w) : Ws s B Z w N :=
  ⟨h.nowrap, h.writable, h.fits, h.wpos, h.wle, h7, h.r8, h9⟩

/-- Between the steps. -/
structure Stg (g : Geo) (s0 : State) (A : Nat → Nat) (live : List Nat) (c : Bool) (s : State) : Prop where
  ws : Ws s g.B g.Z g.w nArr
  keep : Keep g.B g.w (List.range nArr) bodySlots s0.mem s.mem
  rest : Rest bodyRegs s0 s
  cnt : s.mem.readW (off (State.addr g.B) 16) 32 = BitVec.ofNat 32 g.w
  arrs : Arrs s.mem g.B g.w A live
  live_lt : ∀ j ∈ live, j < nArr
  vdTop : w32 s.mem (State.addr g.B) (arr g.w aVD + 4 * g.w) = 0
  mask : slot s.mem g.B sMask = if c then 1 else 0

/-- After a division. -/
structure StgD (g : Geo) (s0 : State) (A : Nat → Nat) (live : List Nat) (c : Bool) (s : State) : Prop where
  ws : WsR s g.B g.Z g.w nArr
  keep : Keep g.B g.w (List.range nArr) bodySlots s0.mem s.mem
  rest : Rest bodyRegs s0 s
  cnt : s.mem.readW (off (State.addr g.B) 16) 32 = BitVec.ofNat 32 g.w
  arrs : Arrs s.mem g.B g.w A live
  live_lt : ∀ j ∈ live, j < nArr
  vdTop : w32 s.mem (State.addr g.B) (arr g.w aVD + 4 * g.w) = 0
  mask : slot s.mem g.B sMask = if c then 1 else 0

theorem slot_eq_of_keep {B : BitVec 32} {w : Nat} {js ds : List Nat} {m m' : Mem} (k : Keep B w js ds m m')
    {e : Nat} (he : e + 4 ≤ hdr) (hd : ∀ d ∈ ds, e + 4 ≤ d ∨ d + 4 ≤ e) :
    m'.readW (off (State.addr B) e) 32 = m.readW (off (State.addr B) e) 32 :=
  BitVec.eq_of_toNat_eq (k.slot he hd)

/-- A step from `Stg`. -/
theorem Stg.next {g : Geo} {s0 s t : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {js ds : List Nat} {rs : List Reg} (hw : Ws t g.B g.Z g.w nArr)
    (k : Keep g.B g.w js ds s.mem t.mem) (hjs : ∀ j ∈ js, j < nArr) (hds : ∀ d ∈ ds, d ∈ bodySlots)
    (r : Rest rs s t) (hrs : ∀ x ∈ rs, x ∈ bodyRegs) {A' : Nat → Nat} {live' : List Nat} {c' : Bool}
    (ha : Arrs t.mem g.B g.w A' live') (hl : ∀ j ∈ live', j < nArr)
    (vd : w32 t.mem (State.addr g.B) (arr g.w aVD + 4 * g.w) = 0)
    (mk : slot t.mem g.B sMask = if c' then 1 else 0) : Stg g s0 A' live' c' t := by
  refine ⟨hw, h.keep.trans (k.mono (fun j hj => List.mem_range.2 (hjs j hj)) hds),
    h.rest.trans (r.mono hrs), ?_, ha, hl, vd, mk⟩
  rw [slot_eq_of_keep k (by decide) (fun d hd => by
    have := hds d hd
    simp only [bodySlots, sB, sC, sT, sF, sMask, List.mem_cons, List.not_mem_nil, or_false] at this
    omega), h.cnt]

/-- The mask through a step that leaves its slot. -/
theorem Stg.mask_keep {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {js ds : List Nat} {m' : Mem} (k : Keep g.B g.w js ds s.mem m')
    (hd : ∀ d ∈ ds, sMask + 4 ≤ d ∨ d + 4 ≤ sMask) : slot m' g.B sMask = if c then 1 else 0 := by
  rw [k.slot (by decide) hd, h.mask]

/-- The top word of `aVD` through a step that leaves `aVD`. -/
theorem Stg.vd_keep {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {js ds : List Nat} {m' : Mem} (k : Keep g.B g.w js ds s.mem m')
    (hj : ∀ j ∈ js, j ≠ aVD) (hd : ∀ d ∈ ds, d + 4 ≤ hdr) :
    w32 m' (State.addr g.B) (arr g.w aVD + 4 * g.w) = 0 := by
  rw [k.word (by simp only [S]; omega) hj hd (h.ws.fit64 (by decide)), h.vdTop]

/-- The arrays through a step that writes none of them. -/
theorem Stg.arrs_keep {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {js ds : List Nat} {m' : Mem} (k : Keep g.B g.w js ds s.mem m')
    (hj : ∀ j ∈ live, j ∉ js) (hd : ∀ d ∈ ds, d + 4 ≤ hdr) : Arrs m' g.B g.w A live :=
  h.arrs.keep k h.ws (fun j hj' => ⟨h.live_lt j hj', hj j hj'⟩) hd

/-- The arrays through a step that writes `o := v`. -/
theorem Stg.arrs_write {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {js ds : List Nat} {m' : Mem} (k : Keep g.B g.w js ds s.mem m') {o v : Nat}
    (e : num m' g.B g.w o = v) (hj : ∀ j ∈ live, j = o ∨ j ∉ js) (hd : ∀ d ∈ ds, d + 4 ≤ hdr) :
    Arrs m' g.B g.w (upd A o v) live :=
  h.arrs.write k h.ws e (fun j hj' => (hj j hj').imp_right fun n => ⟨h.live_lt j hj', n⟩) hd

/-- The mask and'ed with a check. -/
theorem acc_bits {x y : Nat} {c d : Bool} (hx : x = if c then 1 else 0) (hy : y = if d then 1 else 0) :
    (if x = 1 ∧ y = 1 then 1 else 0) = if (c && d) then 1 else 0 := by
  subst hx hy; cases c <;> cases d <;> rfl

theorem bit_le {c : Bool} {x : Nat} (h : x = if c then 1 else 0) : x ≤ 1 := by
  subst h; cases c <;> decide

end VG.Proof.Rsa.Arm.KeyCheck

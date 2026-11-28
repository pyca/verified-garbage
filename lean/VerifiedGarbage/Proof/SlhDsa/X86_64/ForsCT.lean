module

-- separate module: the two-run proofs of `forsSign`, which only the cleanup of signing (`ScrubSign`) needs

public import VerifiedGarbage.Proof.SlhDsa.X86_64.ForsCTBase
public import VerifiedGarbage.Proof.SlhDsa.X86_64.ForsSign
public import VerifiedGarbage.Proof.Framework.RelSplit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SLH-DSA (SHAKE) on x86-64: `forsSign` is constant time, and `Verified`

Two runs of `forsSign` from states of its precondition that agree on its
public data (`scratch`, the signature, the stack pointer) leak the same
trace (`fors_ct`): each loop runs as many times in both (its counters are in
frame 2, at the same values), each call of `thash4` and `levels` has the
same public arguments, and each block is constant time by the taint
analysis (`ForsCTBase.lean`), from the registers both runs agree on, which
a load of a counter from frame 2 adds to by correctness.

The private key values, the key pair and the indices are secret: they reach
only data (the indices through masks).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.Fors

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout setField setFieldR copyWords)
open VG.Impl.SlhDsa.X86_64.Fors
open VG.Proof.SlhDsa (fld)
open VG.Proof.SlhDsa.X86_64.ForsCT (P6)

variable {p : Params}

/-! ## What a part of a body keeps -/

/-- What the parts of a body keep of its entry state `t`: `rbx` = `scratch`,
the stack pointer `sp`, `kp`, the tree's index, the regions, the round
constants and the variables of frame 2. -/
structure Wk (S sp : Addr) (t x : State) : Prop where
  bx : x.gpr .rbx = S
  sp : x.gpr .rsp = sp
  r12 : x.gpr .r12 = t.gpr .r12
  r13 : x.gpr .r13 = t.gpr .r13
  wr : x.wr = t.wr
  rc : RcTable x.mem S
  vars : ∀ q, 2704 ≤ q → q < 2776 → x.mem (at' S q) = t.mem (at' S q)

theorem rc_keep {m m' : Mem} {S : Addr} (h : RcTable m S)
    (hk : ∀ q, 1600 ≤ q → q < 2368 → m' (at' S q) = m (at' S q)) : RcTable m' S := fun r hr k hk' => by
  rw [← h r hr k hk']
  exact Mem.readW_congr fun i hi => by rw [Levels.add_add]; exact hk _ (by omega_using []) (by omega_using [hr, hk', hi])

/-- `Wk` through a part that writes only regions apart from the round
constants and the variables. -/
theorem Wk.frame {S sp : Addr} {t x y : State} (h : Wk S sp t x) {rs : List Region} (f : Frame rs x.mem y.mem)
    (hd : ∀ q, (1600 ≤ q ∧ q < 2368) ∨ (2704 ≤ q ∧ q < 2776) → ∀ r ∈ rs, Region.Disjoint ⟨at' S q, 1⟩ r)
    (hbx : y.gpr .rbx = x.gpr .rbx) (hsp : y.gpr .rsp = x.gpr .rsp) (h12 : y.gpr .r12 = x.gpr .r12)
    (h13 : y.gpr .r13 = x.gpr .r13) (hwr : y.wr = x.wr) : Wk S sp t y :=
  ⟨by rw [hbx, h.bx], by rw [hsp, h.sp], by rw [h12, h.r12], by rw [h13, h.r13], by rw [hwr, h.wr],
    rc_keep h.rc fun q h₁ h₂ => keepS f (hd q (.inl ⟨h₁, h₂⟩)),
    fun q h₁ h₂ => by rw [keepS f (hd q (.inr ⟨h₁, h₂⟩)), h.vars q h₁ h₂]⟩

/-- A variable of frame 2 that `Wk` keeps. -/
theorem Wk.var {S sp : Addr} {t x : State} (h : Wk S sp t x) {i : Nat} (hi : i < 9) :
    x.mem.readW (at' S (Layout.oVar 2 i)) 64 = t.mem.readW (at' S (Layout.oVar 2 i)) 64 :=
  Mem.readW_congr fun j hj => by
    rw [Levels.add_add, oVar2]; exact h.vars _ (by omega_using []) (by omega_using [hi, hj])

/-- Through a call of `thash4`. -/
theorem Wk.t4 {S sp : Addr} {stack : Nat} {t x y : State} (h : Wk S sp t x) {n o st len : Nat}
    (hstk : (below sp stack).Disjoint ⟨S, 2 ^ 16⟩) (ho : 3296 ≤ o) (hon : o + 4 * st ≤ 2 ^ 16)
    (C : T4Post n S stack o st len x y) (hn : 2 * n + 32 ≤ st) : Wk S sp t y := by
  refine h.frame C.frame (fun q hq r hr => ?_) (C.cs _ (by simp [calleeSaved])) (C.cs _ (by simp [calleeSaved]))
    (C.cs _ (by simp [calleeSaved])) (C.cs _ (by simp [calleeSaved])) C.wr
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ⟨k, hk, rfl⟩ | rfl | rfl | rfl
  · have := Nat.mul_le_mul_left st (show k ≤ 3 by omega_using [hk])
    exact dS S (.inl (by simp only [laneAt]; omega_using [hq, ho])) (by omega_using [hq])
      (by simp only [laneAt]; omega_using [this, hon, hn])
  · exact Offset.disjoint_base S (by omega_using [hq]) (by omega_using [hq])
  · exact dS S (by omega_using [hq]) (by omega_using [hq]) (by decide)
  · rw [h.sp]; exact (hstk.sub_right (Levels.sub_scr S (by omega_using [hq]))).symm

/-! ## A call of `thash4` on lanes, in two runs -/

theorem t4g_ct (hp : P6 p) (T : Thash4Impl p.n) (name : String) {stack : Nat} (hst : T.stack + 8 ≤ stack)
    (hs63 : stack < 2 ^ 63) {o st len : Nat}
    (hl' : (o = Layout.oA ∧ st = Layout.strideA) ∨ (o = Layout.oB ∧ st = Layout.strideB))
    (hpos : 0 < len) (hmod : len % 8 = 0) (hle : len ≤ st) {S sp : Addr} {A₁ A₂ : State → Prop}
    (h₁ : ∀ a, A₁ a → Levels.T4Ok S stack a ∧ a.gpr .rsp = sp) (h₂ : ∀ b, A₂ b → Levels.T4Ok S stack b ∧ b.gpr .rsp = sp) :
    RelCT isa (fun a b => A₁ a ∧ A₂ b) (Impl.SlhDsa.X86_64.thashCall ⟨p.n, p.len⟩ name T.code o st len)
      fun _ _ => True := by
  have hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32 := by
    rcases hp with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hl : Lanes o st := by rcases hl' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exacts [.inl ⟨rfl, rfl⟩, .inr ⟨rfl, rfl⟩]
  have hstl := hl.st_lt
  let F : State → Prop := fun u => ∃ t, Levels.T4Ok S stack t ∧ t.gpr .rsp = sp ∧ u.gpr .rdi = at' S o ∧
    u.gpr .rsi = BitVec.ofNat 64 st ∧ u.gpr .rdx = BitVec.ofNat 64 len ∧ u.gpr .rcx = at' S (o + (p.n + 32)) ∧
    u.gpr .r8 = S ∧ (∀ g, g ≠ .rdi → g ≠ .rsi → g ≠ .rdx → g ≠ .rcx → g ≠ .r8 → u.gpr g = t.gpr g) ∧
    u.mem = t.mem ∧ u.wr = t.wr
  have hw : ∀ a, Levels.T4Ok S stack a → a.gpr .rsp = sp →
      WP isa (.block (Impl.SlhDsa.X86_64.thashArgs ⟨p.n, p.len⟩ o st len)) a F := fun a ha hs =>
    targs_ok hn32 hl (by omega_using [hle, hstl]) ha.bx fun u e1 e2 e3 e4 e5 eg em _ ew _ =>
      ⟨a, ha, hs, e1, e2, e3, e4, e5, eg, em, ew⟩
  unfold Impl.SlhDsa.X86_64.thashCall
  refine Levels.relSeq (B₁ := F) (B₂ := F) (ForsCT.ct_fargs hp hl' len fun a b h r hr => ?_)
    (fun a h => hw a (h₁ a h).1 (h₁ a h).2) (fun b h => hw b (h₂ b h).1 (h₂ b h).2) ?_
  · simp only [List.mem_singleton] at hr; subst hr
    rw [(h₁ a h.1).1.bx, (h₂ b h.2).1.bx]
  refine RelCT.call T.verified.1 T.verified.2.1 [] (callG S o st) fun a b ⟨⟨t₁, o₁, s₁, a1, a2, a3, a4, a5, ag, am, aw⟩,
    ⟨t₂, o₂, s₂, b1, b2, b3, b4, b5, bg, bm, bw⟩⟩ => ?_
  obtain ⟨p₁, c₁, w₁⟩ := t4g_entry T hn hst hs63 hl hpos hmod hle o₁.wr o₁.fit o₁.stk o₁.rc a1 a2 a3 a4 a5 ag am aw
  obtain ⟨p₂, c₂, w₂⟩ := t4g_entry T hn hst hs63 hl hpos hmod hle o₂.wr o₂.fit o₂.stk o₂.rc b1 b2 b3 b4 b5 bg bm bw
  have hsp : a.gpr .rsp = b.gpr .rsp := by
    rw [ag _ (by decide) (by decide) (by decide) (by decide) (by decide), s₁,
      bg _ (by decide) (by decide) (by decide) (by decide) (by decide), s₂]
  refine ⟨p₁, p₂, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, c₁, w₁, c₂, w₂, hsp⟩ <;>
    simp only [State.withRegions_gpr, State.callEntry_rsp]
  · rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), a1, b1]
  · rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), a2, b2]
  · rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), a3, b3]
  · rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), a4, b4]
  · rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), a5, b5]
  · rw [hsp]

/-! ## Loads of counters -/

/-- A load of variable `i` of frame 2, `V`. -/
theorem load_ok {S : Addr} {i : Nat} {V : BitVec 64} {t : State} (r : Reg) (hr : r ≠ .rbx) (hi : i < 9)
    (hbx : t.gpr .rbx = S) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr) (hv : t.mem.readW (at' S (Layout.oVar 2 i)) 64 = V) :
    WP isa (.block [.mov r (.mem (var i))]) t fun x => x.gpr .rbx = S ∧ x.gpr r = V :=
  Proof.Sha3.X86_64.wp_movm (a := at' S (Layout.oVar 2 i)) (by rw [var, Proof.Sha3.X86_64.ea_at, hbx])
    (Levels.in_scr' hw (by rw [oVar2]; omega_using [hi])) fun x e => WP.block_nil
      ⟨by rw [e.other _ (Ne.symm hr), hbx], by rw [e.gpr, hv]⟩

/-- A block whose first instruction loads variable `i`, which the rest uses
in addresses, in two runs where it is the same `V`. -/
theorem load_ct {S : Addr} {i : Nat} {V : BitVec 64} {A₁ A₂ : State → Prop} (r : Reg) (hr : r ≠ .rbx) (hi : i < 9)
    {l : List Instr}
    (h₁ : ∀ a, A₁ a → a.gpr .rbx = S ∧ (⟨S, 2 ^ 16⟩ : Region) ∈ a.wr ∧ a.mem.readW (at' S (Layout.oVar 2 i)) 64 = V)
    (h₂ : ∀ b, A₂ b → b.gpr .rbx = S ∧ (⟨S, 2 ^ 16⟩ : Region) ∈ b.wr ∧ b.mem.readW (at' S (Layout.oVar 2 i)) 64 = V)
    (hct : ∀ {P : State → State → Prop}, (∀ x y, P x y → ∀ r' ∈ [Reg.rbx, r], x.gpr r' = y.gpr r') →
      RelCT isa P (.block l) fun _ _ => True) :
    RelCT isa (fun a b => A₁ a ∧ A₂ b) (.block (([.mov r (.mem (var i))] : List Instr) ++ l)) fun _ _ => True := by
  refine RelCT.block_append (Levels.relSeq (ct_load r i fun x y ⟨hx, hy⟩ r' hr' => ?_)
    (fun a ha => load_ok r hr hi (h₁ a ha).1 (h₁ a ha).2.1 (h₁ a ha).2.2)
    (fun b hb => load_ok r hr hi (h₂ b hb).1 (h₂ b hb).2.1 (h₂ b hb).2.2) (hct fun x y ⟨hx, hy⟩ r' hr' => ?_))
  · simp only [List.mem_singleton] at hr'; subst hr'; rw [(h₁ x hx).1, (h₂ y hy).1]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · rw [hx.1, hy.1]
    · rw [hx.2, hy.2]

/-! ## Four leaves, in two runs -/

/-- What `leaf_ok` needs of the state before four leaves. -/
structure LeafH (p : Params) (stack : Nat) (S AU sp : Addr) (pkSeed a16 skSeed : List Byte) (KP : BitVec 64)
    (V4 U2 J idx : Nat) (t : State) : Prop where
  bx : t.gpr .rbx = S
  r12 : t.gpr .r12 = KP
  kp : KP.toNat < 2 ^ 32
  r13 : t.gpr .r13 = BitVec.ofNat 64 idx
  idx : idx < 2 ^ 32
  w : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr
  fit : S.toNat + 2 ^ 16 ≤ 2 ^ 64
  rsp : t.gpr .rsp = sp
  stk : (below sp stack).Disjoint ⟨S, 2 ^ 16⟩
  env : Env p t.mem S pkSeed a16
  sk : SkAt p t.mem S skSeed
  v1 : t.mem.readW (at' S (Layout.oVar 2 1)) 64 = AU
  v2 : t.mem.readW (at' S (Layout.oVar 2 2)) 64 = BitVec.ofNat 64 U2
  v3 : t.mem.readW (at' S (Layout.oVar 2 3)) 64 = BitVec.ofNat 64 J
  v4 : t.mem.readW (at' S (Layout.oVar 2 4)) 64 = BitVec.ofNat 64 V4
  X : V4 + U2 + J + 4 < 2 ^ 32
  J : (J + 4) * p.n ≤ 32 * Layout.nodeSlots
  out : ∀ w < p.n / 8, InRegions t.wr (AU + BitVec.ofNat 64 (8 * w)) 8
  d : Region.Disjoint ⟨AU, p.n⟩ ⟨S, Layout.oSigTmp⟩
  As : Region.Disjoint ⟨AU, p.n⟩ (below sp stack)

theorem LeafH.wk {stack : Nat} {S AU sp : Addr} {pkSeed a16 skSeed : List Byte} {KP : BitVec 64} {V4 U2 J idx : Nat}
    {t : State} (H : LeafH p stack S AU sp pkSeed a16 skSeed KP V4 U2 J idx t) : Wk S sp t t :=
  ⟨H.bx, H.rsp, rfl, rfl, rfl, H.env.rc, fun _ _ _ => rfl⟩

/-- `Wk` through the capture of the private key values. -/
theorem Wk.cap {S sp AU : Addr} {t x y : State} {n C idx : Nat} (h : Wk S sp t x) (hn : n ≤ 32)
    (hd : Region.Disjoint ⟨AU, n⟩ ⟨S, Layout.oSigTmp⟩) (B : CapP n S AU x y C idx) : Wk S sp t y := by
  refine h.frame B.frame (fun q hq r hr => ?_) (B.gpr _ (by decide) (by decide) (by decide) (by decide))
    (B.gpr _ (by decide) (by decide) (by decide) (by decide)) (B.gpr _ (by decide) (by decide) (by decide) (by decide))
    (B.gpr _ (by decide) (by decide) (by decide) (by decide)) B.wr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact (hd.sub_right (Offset.sub_base S (by rw [show Layout.oSigTmp = 31648 from rfl]; omega_using [hq]))).symm
  · simp only [typeRs, List.mem_map, List.mem_range] at hr
    obtain ⟨k, hk, rfl⟩ := hr
    exact dS S (.inl (by rw [laneA_eq]; omega_using [hq])) (by omega_using [hq]) (by rw [laneA_eq]; omega_using [hk, hn])

theorem leaf_ct (hp : FSet p) (T : Thash4Impl p.n) (name : String) {stack : Nat} (hst : T.stack + 8 ≤ stack)
    (hs63 : stack < 2 ^ 63) {S AU sp : Addr} {V4 U2 J : Nat} {pk₁ a₁ sk₁ pk₂ a₂ sk₂ : List Byte}
    {KP₁ KP₂ : BitVec 64} {idx₁ idx₂ : Nat} :
    RelCT isa (fun a b => LeafH p stack S AU sp pk₁ a₁ sk₁ KP₁ V4 U2 J idx₁ a ∧
        LeafH p stack S AU sp pk₂ a₂ sk₂ KP₂ V4 U2 J idx₂ b)
      (leafBody ⟨p.n, p.len⟩ p.a name T.code) fun _ _ => True := by
  obtain ⟨hf, hn, -, -, -, -, -, -⟩ := hp.facts
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hn8 : p.n % 8 = 0 := by omega_using [hn]
  have hp6 : P6 p := hp.2
  -- in each run, what the parts keep
  have sA : ∀ {pk a sk : List Byte} {KP : BitVec 64} {idx : Nat} (x : State),
      LeafH p stack S AU sp pk a sk KP V4 U2 J idx x →
      WP isa (.block (([.mov .r10 (.mem (var 4)), .alu .add .r10 (.mem (var 2)), .alu .add .r10 (.mem (var 3))] : List Instr) ++
        (List.range 4).flatMap (fun k => leafAdrs ⟨p.n, p.len⟩ 6 k ++
          copyWords .rbx (Layout.laneA k + (⟨p.n, p.len⟩ : Layout).msgOff) .rbx Layout.oSkSeed (p.n / 8)))) x
        fun y => ∃ x, LeafH p stack S AU sp pk a sk KP V4 U2 J idx x ∧ Wk S sp x y := fun x H =>
    WP.mono (lanesA_ok hn H.bx H.r12 H.kp H.w H.v4 H.v2 H.v3 (by omega_using [H.X])) fun y A =>
      ⟨x, H, H.wk.frame A.frame (fun q hq r hr => by
        simp only [laneRs, List.mem_map, List.mem_range] at hr
        obtain ⟨k, hk, rfl⟩ := hr
        exact dS S (.inl (by rw [laneA_eq]; omega_using [hq])) (by omega_using [hq])
          (by rw [laneA_eq]; omega_using [hk, hn32]))
        (A.gpr _ (by decide) (by decide) (by decide)) (A.gpr _ (by decide) (by decide) (by decide))
        (A.gpr _ (by decide) (by decide) (by decide)) (A.gpr _ (by decide) (by decide) (by decide)) A.wr⟩
  have sT : ∀ {pk a sk : List Byte} {KP : BitVec 64} {idx : Nat} (y : State),
      (∃ x, LeafH p stack S AU sp pk a sk KP V4 U2 J idx x ∧ Wk S sp x y) →
      Levels.T4Ok S stack y ∧ y.gpr .rsp = sp := fun y ⟨x, H, W⟩ =>
    ⟨⟨W.bx, by rw [W.wr]; exact H.w, H.fit, by rw [W.sp]; exact H.stk, W.rc⟩, W.sp⟩
  have sC : ∀ {pk a sk : List Byte} {KP : BitVec 64} {idx : Nat} (y : State),
      (∃ x, LeafH p stack S AU sp pk a sk KP V4 U2 J idx x ∧ Wk S sp x y) →
      WP isa (Impl.SlhDsa.X86_64.thashCall ⟨p.n, p.len⟩ name T.code Layout.oA Layout.strideA (2 * p.n + 32)) y
        fun z => ∃ x, LeafH p stack S AU sp pk a sk KP V4 U2 J idx x ∧ Wk S sp x z := fun y ⟨x, H, W⟩ =>
    WP.mono (t4g_ok T name hn hst hs63 (o := Layout.oA) (st := Layout.strideA) (len := 2 * p.n + 32)
      (.inl ⟨rfl, rfl⟩) (by omega_using []) (by omega_using [hn8]) (by simp only [Layout.strideA]; omega_using [hn32])
      W.bx (by rw [W.wr]; exact H.w) H.fit (by rw [W.sp]; exact H.stk) W.rc) fun z C =>
      ⟨x, H, W.t4 H.stk (by decide) (by decide) C (by simp only [Layout.strideA]; omega_using [hn32])⟩
  have sB : ∀ {pk a sk : List Byte} {KP : BitVec 64} {idx : Nat} (y : State),
      (∃ x, LeafH p stack S AU sp pk a sk KP V4 U2 J idx x ∧ Wk S sp x y) →
      WP isa (.block (([.mov .rsi (.mem (var 1)), .mov .rdx (.mem (var 2)), .alu .add .rdx (.mem (var 3))] : List Instr) ++
        (List.range 4).flatMap (captureSk ⟨p.n, p.len⟩) ++
        (List.range 4).flatMap (fun k => setField .rbx (Layout.laneA k + (⟨p.n, p.len⟩ : Layout).adrsOff + 16) 3))) y
        fun z => ∃ x, LeafH p stack S AU sp pk a sk KP V4 U2 J idx x ∧ Wk S sp x z := fun y ⟨x, H, W⟩ =>
    WP.mono (capB_ok (U2 := U2) (J := J) hn W.bx (by rw [W.r13, H.r13]) (by rw [W.wr]; exact H.w)
      (by rw [W.var (by decide), H.v1]) (by rw [W.var (by decide), H.v2]) (by rw [W.var (by decide), H.v3])
      (by omega_using [H.X]) H.idx (fun w hw => by rw [W.wr]; exact H.out w hw) H.d) fun z B =>
      ⟨x, H, W.cap hn32 H.d B⟩
  have hv : ∀ {pk a sk : List Byte} {KP : BitVec 64} {idx : Nat} {i : Nat} {V : BitVec 64}, i < 9 →
      (∀ x, LeafH p stack S AU sp pk a sk KP V4 U2 J idx x → x.mem.readW (at' S (Layout.oVar 2 i)) 64 = V) →
      ∀ y, (∃ x, LeafH p stack S AU sp pk a sk KP V4 U2 J idx x ∧ Wk S sp x y) →
        y.gpr .rbx = S ∧ (⟨S, 2 ^ 16⟩ : Region) ∈ y.wr ∧ y.mem.readW (at' S (Layout.oVar 2 i)) 64 = V :=
    fun hi hV y ⟨x, H, W⟩ => ⟨W.bx, by rw [W.wr]; exact H.w, by rw [W.var hi]; exact hV x H⟩
  unfold leafBody
  refine Levels.relSeq (ct_lanesA hp6 fun x y ⟨hx, hy⟩ r hr => ?_) (fun x h => sA x h) (fun x h => sA x h) ?_
  · simp only [List.mem_singleton] at hr; subst hr; rw [hx.bx, hy.bx]
  refine Levels.relSeq (t4g_ct hp6 T name hst hs63 (.inl ⟨rfl, rfl⟩) (by dsimp only; omega_using [])
    (by dsimp only; omega_using [hn8]) (by dsimp only; simp only [Layout.strideA]; omega_using [hn32])
    (fun y h => sT y h) (fun y h => sT y h))
    (fun y h => sC y h) (fun y h => sC y h) ?_
  refine Levels.relSeq (load_ct .rsi (by decide) (by decide) (i := 1) (V := AU) (hv (by decide) fun x H => H.v1)
    (hv (by decide) fun x H => H.v1) (ct_capture hp6)) (fun y h => sB y h) (fun y h => sB y h) ?_
  refine Levels.relSeq (t4g_ct hp6 T name hst hs63 (.inl ⟨rfl, rfl⟩) (by dsimp only; omega_using [])
    (by dsimp only; omega_using [hn8]) (by dsimp only; simp only [Layout.strideA]; omega_using [hn32])
    (fun y h => sT y h) (fun y h => sT y h))
    (fun y h => sC y h) (fun y h => sC y h) ?_
  exact load_ct .rdx (by decide) (by decide) (i := 3) (V := BitVec.ofNat 64 J) (hv (by decide) fun x H => H.v3)
    (hv (by decide) fun x H => H.v3) (ct_out hp6)

/-! ## The loop of leaves, in two runs -/

/-- What the loop of leaves needs of its entry state `t₀`. -/
structure LoopC (p : Params) (stack : Nat) (S AU : Addr) (KP : BitVec 64) (V4 U2 idx : Nat) (t₀ : State) : Prop where
  bx : t₀.gpr .rbx = S
  r12 : t₀.gpr .r12 = KP
  kp : KP.toNat < 2 ^ 32
  r13 : t₀.gpr .r13 = BitVec.ofNat 64 idx
  idx : idx < 2 ^ 32
  w : (⟨S, 2 ^ 16⟩ : Region) ∈ t₀.wr
  fit : S.toNat + 2 ^ 16 ≤ 2 ^ 64
  stk : (below (t₀.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩
  X : V4 + U2 + 2 ^ s p.a < 2 ^ 32
  out : ∀ w < p.n / 8, InRegions t₀.wr (AU + BitVec.ofNat 64 (8 * w)) 8
  d : Region.Disjoint ⟨AU, p.n⟩ ⟨S, Layout.oSigTmp⟩
  As : Region.Disjoint ⟨AU, p.n⟩ (below (t₀.gpr .rsp) stack)

theorem ls_leafH (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {stack : Nat} {S AU : Addr} {KP : BitVec 64}
    {V4 U2 idx : Nat} {pkSeed a16 skSeed : List Byte} {t₀ : State} (C : LoopC p stack S AU KP V4 U2 idx t₀)
    {m : Nat} {u : State} (hI : LI p stack S AU pkSeed a16 skSeed KP.toNat V4 U2 idx t₀ m u) :
    LeafH p stack S AU (t₀.gpr .rsp) pkSeed a16 skSeed KP V4 U2 (2 ^ s p.a - 4 * m) idx u := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hs9 : s p.a ≤ 9 := Nat.min_le_right _ _
  have h512 : 2 ^ s p.a ≤ 512 := by
    calc 2 ^ s p.a ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hs9
      _ = 512 := rfl
  obtain ⟨J, hJ, hm, L⟩ := hI
  obtain rfl : J = 2 ^ s p.a - 4 * m := by omega_using [hJ]
  have hJ4 : (2 ^ s p.a - 4 * m + 4) * p.n ≤ 32 * Layout.nodeSlots := by
    have := Nat.mul_le_mul_right p.n (show 2 ^ s p.a - 4 * m + 4 ≤ 520 by omega_using [hJ, hm, h512])
    rw [show Layout.nodeSlots = 520 from rfl]; omega_using [this, hn32]
  have hcs : ∀ r ∈ calleeSaved, u.gpr r = t₀.gpr r := L.fix.cs
  exact ⟨by rw [hcs _ (by simp [calleeSaved]), C.bx], by rw [hcs _ (by simp [calleeSaved]), C.r12], C.kp,
    by rw [hcs _ (by simp [calleeSaved]), C.r13], C.idx, by rw [L.fix.wr]; exact C.w, C.fit,
    hcs _ (by simp [calleeSaved]), C.stk, L.env, L.sk, L.v1, L.v2, L.v3, L.v4, by omega_using [C.X, hJ, hm], hJ4,
    fun w hw => by rw [L.fix.wr]; exact C.out w hw, C.d, C.As⟩

theorem leaves_ct (hp : FSet p) (T : Thash4Impl p.n) (name : String) {stack : Nat} (hst : T.stack + 8 ≤ stack)
    (hs63 : stack < 2 ^ 63) {S AU : Addr} {V4 U2 : Nat} {pk₁ a₁ sk₁ pk₂ a₂ sk₂ : List Byte}
    {KP₁ KP₂ : BitVec 64} {idx₁ idx₂ : Nat} {t₁ t₂ : State} (C₁ : LoopC p stack S AU KP₁ V4 U2 idx₁ t₁)
    (C₂ : LoopC p stack S AU KP₂ V4 U2 idx₂ t₂) (hsp : t₁.gpr .rsp = t₂.gpr .rsp) (m : Nat) :
    RelCT isa (fun a b => LI p stack S AU pk₁ a₁ sk₁ KP₁.toNat V4 U2 idx₁ t₁ m a ∧
        LI p stack S AU pk₂ a₂ sk₂ KP₂.toNat V4 U2 idx₂ t₂ m b)
      (.loop (leafBody ⟨p.n, p.len⟩ p.a name T.code) .b) fun a b =>
        LS p stack S AU pk₁ a₁ sk₁ KP₁.toNat V4 U2 idx₁ t₁ (2 ^ s p.a) a ∧
        LS p stack S AU pk₂ a₂ sk₂ KP₂.toNat V4 U2 idx₂ t₂ (2 ^ s p.a) b := by
  obtain ⟨hf, hn, -, -, -, -, -, -⟩ := hp.facts
  refine Levels.relLoop (fun m => decide (1 < m)) (fun m => m - 1) (fun m => RelCT.mono (leaf_ct hp T name hst hs63)
      (fun a b ⟨ha, hb⟩ => ⟨ls_leafH hn C₁ ha, by have := ls_leafH hn C₂ hb; rw [← hsp] at this; exact this⟩)
      fun _ _ h => h)
    (leaves_step T name hn hf hst hs63 C₁.bx C₁.r12 C₁.kp C₁.r13 C₁.idx C₁.w C₁.fit C₁.stk C₁.X C₁.out C₁.d C₁.As)
    (leaves_step T name hn hf hst hs63 C₂.bx C₂.r12 C₂.kp C₂.r13 C₂.idx C₂.w C₂.fit C₂.stk C₂.X C₂.out C₂.d C₂.As) m

/-! ## The heights of a subtree, in two runs -/

/-- `levels`'s public data, from the same arguments. -/
theorem lpub {stk : Nat} {v₁ v₂ : State} {W : List Region}
    (h1 : v₁.gpr .rdi = v₂.gpr .rdi) (h2 : v₁.gpr .rsi = v₂.gpr .rsi) (h3 : v₁.gpr .rdx = v₂.gpr .rdx)
    (h4 : v₁.gpr .rcx = v₂.gpr .rcx) (h5 : v₁.gpr .r8 = v₂.gpr .r8) (h6 : v₁.gpr .rsp = v₂.gpr .rsp) :
    (levelsContract p stk).pub (v₁.callEntry.withRegions [] W) (v₂.callEntry.withRegions [] W) := by
  simp only [levelsContract, State.withRegions_gpr]
  rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
    State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
    State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
    State.callEntry_gpr _ (by decide), State.callEntry_rsp, State.callEntry_rsp, h1, h2, h3, h4, h5, h6]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- What the heights of a subtree need of the state before them. -/
structure SubHH (p : Params) (stack : Nat) (S SG AU sp : Addr) (L dA U2 V4 idx : Nat) (pkSeed a16 : List Byte)
    (u : State) : Prop where
  bx : u.gpr .rbx = S
  kp : (u.gpr .r12).toNat < 2 ^ 32
  r13 : u.gpr .r13 = BitVec.ofNat 64 idx
  idx : idx < 2 ^ 32
  w : (⟨S, 2 ^ 16⟩ : Region) ∈ u.wr
  wG : (⟨SG, L⟩ : Region) ∈ u.wr
  hAU : AU = SG + BitVec.ofNat 64 dA
  hdA : dA + p.n + s p.a * p.n ≤ L
  Gf : SG.toNat + L ≤ 2 ^ 64
  fit : S.toNat + 2 ^ 16 ≤ 2 ^ 64
  rsp : u.gpr .rsp = sp
  stk : (below sp stack).Disjoint ⟨S, 2 ^ 16⟩
  Gd : Region.Disjoint ⟨SG, L⟩ ⟨S, Layout.oSigTmp⟩
  Gs : Region.Disjoint ⟨SG, L⟩ (below sp stack)
  env : Env p u.mem S pkSeed a16
  v1 : u.mem.readW (at' S (Layout.oVar 2 1)) 64 = AU
  v2 : u.mem.readW (at' S (Layout.oVar 2 2)) 64 = BitVec.ofNat 64 U2
  v4 : u.mem.readW (at' S (Layout.oVar 2 4)) 64 = BitVec.ofNat 64 V4
  X : V4 + U2 < 2 ^ 32
  s6 : 6 ≤ s p.a

/-- After the parameters of `levels`: its precondition, and what its call
leaves for the root's copy. -/
theorem subH_call (T : Thash4Impl p.n) (name ln : String) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
    (hf : p.family = .shake) {stack : Nat} (hst : T.stack + 24 ≤ stack) (hs63 : stack < 2 ^ 63)
    {S SG AU sp : Addr} {L dA U2 V4 idx : Nat} {pkSeed a16 : List Byte} {u u₁ : State}
    (H : SubHH p stack S SG AU sp L dA U2 V4 idx pkSeed a16 u)
    (B : LB p.n S u u₁ (2 ^ s p.a) 0 (AU + BitVec.ofNat 64 p.n) (BitVec.ofNat 64 U2) (BitVec.ofNat 64 (V4 + U2))
      (BitVec.ofNat 64 3) (u.gpr .r12)) :
    (levelsContract p (stack - 8)).pre
        (u₁.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨AU + BitVec.ofNat 64 p.n, s p.a * p.n⟩]) ∧
      Covers ([] ++ [⟨S, scratchLen⟩, ⟨AU + BitVec.ofNat 64 p.n, s p.a * p.n⟩]) (u₁.rd ++ u₁.wr) ∧
      Covers [⟨S, scratchLen⟩, ⟨AU + BitVec.ofNat 64 p.n, s p.a * p.n⟩] u₁.wr ∧
      WP isa (.call ln (Impl.SlhDsa.X86_64.Tree.levels ⟨p.n, p.len⟩ name T.code)) u₁ fun v' =>
        v'.gpr .rbx = S ∧ (⟨S, 2 ^ 16⟩ : Region) ∈ v'.wr ∧
          v'.mem.readW (at' S (Layout.oVar 2 2)) 64 = BitVec.ofNat 64 U2 := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hs9 : s p.a ≤ 9 := Nat.min_le_right _ _
  have h512 : 2 ^ s p.a ≤ 512 := by
    calc 2 ^ s p.a ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hs9
      _ = 512 := rfl
  have hs6 := H.s6
  have hsn : 1 ≤ s p.a * p.n := Nat.mul_pos (by omega_using [hs6]) (by omega_using [hn])
  have hcnt : (2 ^ s p.a + 8) * p.n ≤ 32 * Layout.nodeSlots := by
    have := Nat.mul_le_mul (show 2 ^ s p.a + 8 ≤ 520 by omega_using [h512]) hn32
    rw [show Layout.nodeSlots = 520 from rfl]; omega_using [this]
  have kB : ∀ q, q < 2 ^ 16 → (q < 3000 ∨ 3032 ≤ q) → u₁.mem (at' S q) = u.mem (at' S q) := fun q hq h =>
    keepS B.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact dS S (by rw [oVar4]; omega_using [h]) (by omega_using [hq]) (by rw [oVar4]; omega_using [])
  have hE₁ : Env p u₁.mem S pkSeed a16 := env_bytes hn32 H.env fun q hq => kB q
    (by simp only [EnvB] at hq; omega_using [hq]) (by simp only [EnvB] at hq; omega_using [hq])
  have hsp₁ : u₁.gpr .rsp = sp := by
    rw [B.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), H.rsp]
  have hAU' : AU + BitVec.ofNat 64 p.n = SG + BitVec.ofNat 64 (dA + p.n) := by rw [H.hAU, Levels.add_add]
  have hsubA : Region.Sub ⟨AU + BitVec.ofNat 64 p.n, s p.a * p.n⟩ ⟨SG, L⟩ := by
    rw [hAU']; exact Offset.sub_base SG (by omega_using [H.hdA])
  have ht : ∀ (x : Nat), x < 2 ^ 32 → (BitVec.ofNat 64 x).toNat = x := fun x hx => by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hx])
  have hvA : ∀ i, 5 ≤ i → i ≤ 8 → (varAt u₁.mem S 4 i).toNat < 2 ^ 32 := fun i h₁ h₂ => by
    simp only [varAt]
    rcases (show i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 by omega_using [h₁, h₂]) with rfl | rfl | rfl | rfl
    · rw [B.v5, ht _ (by omega_using [H.X])]; omega_using [H.X]
    · rw [B.v6, ht _ H.X]; exact H.X
    · rw [B.v7]; decide
    · rw [B.v8]; exact H.kp
  have hr9 : (u₁.gpr .r9).toNat < 2 ^ 32 := by rw [B.r9, H.r13, ht _ H.idx]; exact H.idx
  have hstk₁ : (below (u₁.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩ := by rw [hsp₁]; exact H.stk
  have hAf : (AU + BitVec.ofNat 64 p.n).toNat + s p.a * p.n ≤ 2 ^ 64 := by
    rw [hAU', Levels.toNat_at (by omega_using [H.Gf, H.hdA, hsn])]; omega_using [H.Gf, H.hdA]
  have hAs : Region.Disjoint ⟨AU + BitVec.ofNat 64 p.n, s p.a * p.n⟩ (below (u₁.gpr .rsp) stack) := by
    rw [hsp₁]; exact H.Gs.sub_left hsubA
  obtain ⟨hpre, hc, hw⟩ := lcall_pre T hn hst hs63 (h := s p.a) (z₀ := 0) (L := L) (d := dA + p.n)
    B.rdi B.rsi B.rdx B.rcx B.r8 hr9 (by omega_using [hs6]) (by omega_using [hs9]) hcnt
    (by rw [B.wr]; exact H.w) (by rw [B.wr]; exact H.wG) hAU' (by omega_using [H.hdA]) H.fit hstk₁ hAf
    (H.Gd.sub_left hsubA) hAs hE₁ hvA
  refine ⟨hpre, hc, hw, lcall_ok T name ln hn hf hst hs63 (h := s p.a) (z₀ := 0) (L := L) (d := dA + p.n)
    B.rdi B.rsi B.rdx B.rcx B.r8 hr9 (by omega_using [hs6]) (by omega_using [hs9]) hcnt
    (by rw [B.wr]; exact H.w) (by rw [B.wr]; exact H.wG) hAU' (by omega_using [H.hdA]) H.fit hstk₁ hAf
    (H.Gd.sub_left hsubA) hAs hE₁ hvA fun v' fx _ _ _ fr => ⟨?_, ?_, ?_⟩⟩
  · rw [fx.cs _ (by simp [calleeSaved]), B.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), H.bx]
  · rw [fx.wr, B.wr]; exact H.w
  · rw [← H.v2]
    refine Mem.readW_congr fun j hj => ?_
    rw [Levels.add_add, oVar2, ← kB (2704 + 8 * 2 + j) (by omega_using [hj]) (by omega_using [hj])]
    refine keepS fr fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · simp only [levelsChanges, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with ⟨k, hk, rfl⟩ | rfl | rfl | rfl | rfl
      · exact dS S (.inl (by rw [laneA_eq]; omega_using [hj])) (by omega_using [hj]) (by rw [laneA_eq]; omega_using [hk, hn32])
      · exact Offset.disjoint_base S (by omega_using []) (by omega_using [hj])
      · exact dS S (.inr (by omega_using [])) (by omega_using [hj]) (by decide)
      · exact dS S (.inl (by rw [show Layout.oFrame 4 = 2912 from rfl]; omega_using [hj])) (by omega_using [hj]) (by decide)
      · exact dS S (.inl (by rw [show Layout.oN = 12640 from rfl]; omega_using [hj])) (by omega_using [hj])
          (by rw [show Layout.oN = 12640 from rfl]; rw [show Layout.nodeSlots = 520 from rfl] at hcnt; omega_using [hcnt])
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dqlow (H.Gd.sub_left hsubA) (by omega_using [hj])
      · exact (hstk₁.sub_right (Levels.sub_scr S (by omega_using [hj]))).symm

theorem subH_ct (hp : FSet p) (T : Thash4Impl p.n) (name ln : String) {stack : Nat} (hst : T.stack + 24 ≤ stack)
    (hs63 : stack < 2 ^ 63) {S SG AU sp : Addr} {L dA U2 V4 idx₁ idx₂ : Nat} {pk₁ a₁ pk₂ a₂ : List Byte} :
    RelCT isa (fun a b => SubHH p stack S SG AU sp L dA U2 V4 idx₁ pk₁ a₁ a ∧ SubHH p stack S SG AU sp L dA U2 V4 idx₂ pk₂ a₂ b)
      (subtreeHeights ⟨p.n, p.len⟩ p.a name ln T.code) fun _ _ => True := by
  obtain ⟨hf, hn, -, -, -, -, -, -⟩ := hp.facts
  have hp6 : P6 p := hp.2
  let B : Nat → List Byte → List Byte → State → Prop := fun idx pk a y => ∃ x, SubHH p stack S SG AU sp L dA U2 V4 idx pk a x ∧
    LB p.n S x y (2 ^ s p.a) 0 (AU + BitVec.ofNat 64 p.n) (BitVec.ofNat 64 U2) (BitVec.ofNat 64 (V4 + U2))
      (BitVec.ofNat 64 3) (x.gpr .r12)
  have sB : ∀ {idx pk a} (x : State), SubHH p stack S SG AU sp L dA U2 V4 idx pk a x →
      WP isa (.block (([.mov .r10 (.mem (var 1)), .alu .add .r10 (.imm (BitVec.ofNat 32 (⟨p.n, p.len⟩ : Layout).n)),
        .mov .rcx (.mem (var 4)), .alu .add .rcx (.mem (var 2))] : List Instr) ++
        Impl.SlhDsa.X86_64.Tree.setParams (.mem (var 2)) (.reg .rcx) (.imm 3) (.reg .r12) ++
        ([.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 Layout.oN)),
          .mov32 .rdx (.imm (BitVec.ofNat 32 (2 ^ s p.a))), .mov32 .rcx (.imm 0),
          .mov .r8 (.reg .r10), .mov .r9 (.reg .r13)] : List Instr))) x (B idx pk a) := fun x H =>
    WP.mono (subB_ok hn H.bx H.w H.v1 H.v2 H.v4) fun y hy => ⟨x, H, hy⟩
  have hsp : ∀ {idx pk a} y, B idx pk a y → y.gpr .rsp = sp := fun y ⟨x, H, hB⟩ => by
    rw [hB.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), H.rsp]
  unfold subtreeHeights
  refine Levels.relSeq (ct_subB hp6 fun x y ⟨hx, hy⟩ r hr => ?_) (fun x h => sB x h) (fun x h => sB x h) ?_
  · simp only [List.mem_singleton] at hr; subst hr; rw [hx.bx, hy.bx]
  refine Levels.relSeq (B₁ := fun v => v.gpr .rbx = S ∧ (⟨S, 2 ^ 16⟩ : Region) ∈ v.wr ∧
      v.mem.readW (at' S (Layout.oVar 2 2)) 64 = BitVec.ofNat 64 U2) (B₂ := fun v => v.gpr .rbx = S ∧
      (⟨S, 2 ^ 16⟩ : Region) ∈ v.wr ∧ v.mem.readW (at' S (Layout.oVar 2 2)) 64 = BitVec.ofNat 64 U2)
    (RelCT.call (Levels.levels_correct T name hn hf (stack := stack - 8) (by omega_using [hst]) (by omega_using [hs63]))
      (Levels.levels_ct T name hn hf (by omega_using [hst]) (by omega_using [hs63])) []
      [⟨S, scratchLen⟩, ⟨AU + BitVec.ofNat 64 p.n, s p.a * p.n⟩] fun x y ⟨hx, hy⟩ => ?_)
    (fun x ⟨x₀, H, hB⟩ => (subH_call T name ln hn hf hst hs63 H hB).2.2.2)
    (fun y ⟨y₀, H, hB⟩ => (subH_call T name ln hn hf hst hs63 H hB).2.2.2)
    (load_ct .rdx (by decide) (by decide) (fun v h => h) (fun v h => h) (ct_rootCopy hp6))
  obtain ⟨x₀, Hx, Bx⟩ := hx
  obtain ⟨y₀, Hy, By⟩ := hy
  obtain ⟨px, cx, wx, -⟩ := subH_call T name ln hn hf hst hs63 Hx Bx
  obtain ⟨py, cy, wy, -⟩ := subH_call T name ln hn hf hst hs63 Hy By
  refine ⟨px, py, lpub (by rw [Bx.rdi, By.rdi]) (by rw [Bx.rsi, By.rsi]) (by rw [Bx.rdx, By.rdx])
    (by rw [Bx.rcx, By.rcx]) (by rw [Bx.r8, By.r8]) (by rw [hsp x ⟨x₀, Hx, Bx⟩, hsp y ⟨y₀, Hy, By⟩]),
    cx, wx, cy, wy, by rw [hsp x ⟨x₀, Hx, Bx⟩, hsp y ⟨y₀, Hy, By⟩]⟩

/-! ## A subtree, in two runs -/

/-- The block before the leaves, in one run: the loop of leaves' entry. -/
theorem sub_s1 {stack : Nat} {S SG AU : Addr} {L dA tt idx : Nat} {pkSeed a16 skSeed : List Byte} {t₀ : State}
    (C : SC p stack S SG AU L dA tt idx t₀) {u : Nat} (hu : u < 2 ^ (p.a - s p.a)) {t : State}
    (hI : ST p stack S AU pkSeed a16 skSeed (t₀.gpr .r12).toNat tt idx t₀ u t) :
    WP isa (.block [.mov32 .rax (.imm 0), .store (var 3) .rax]) t fun t₁ => Fix t₀ t₁ ∧
      LoopC p stack S AU (t₀.gpr .r12) (tt * 2 ^ p.a) (u * 2 ^ s p.a) idx t₁ ∧
      LS p stack S AU pkSeed a16 skSeed (t₀.gpr .r12).toNat (tt * 2 ^ p.a) (u * 2 ^ s p.a) idx t₁ 0 t₁ := by
  have hn := C.hn
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hsa := s_le p.a
  have h2a : 2 ^ p.a ≤ 2 ^ 14 := Nat.pow_le_pow_right (by decide) C.a14
  have hUs : 2 ^ (p.a - s p.a) * 2 ^ s p.a = 2 ^ p.a := by rw [← Nat.pow_add, Nat.sub_add_cancel hsa]
  have hu1 : (u + 1) * 2 ^ s p.a ≤ 2 ^ p.a := by rw [← hUs]; exact Nat.mul_le_mul_right _ hu
  have hu1' : u * 2 ^ s p.a + 2 ^ s p.a ≤ 2 ^ p.a := by rw [← Nat.succ_mul]; exact hu1
  have hdAn : dA + (p.a + 1) * p.n ≤ L := C.dA
  have han : (p.a + 1) * p.n = p.n + p.a * p.n := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
  have hsp : t.gpr .rsp = t₀.gpr .rsp := hI.fix.cs _ (by simp [calleeSaved])
  have hbx : t.gpr .rbx = S := by rw [hI.fix.cs _ (by simp [calleeSaved]), C.bx]
  have hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr := by rw [hI.fix.wr]; exact C.w
  have dXs : ∀ {o l : Nat}, o + l ≤ (p.a + 1) * p.n → ∀ {R : Region}, Region.Sub R ⟨S, Layout.oSigTmp⟩ →
      Region.Disjoint ⟨AU + BitVec.ofNat 64 o, l⟩ R := fun {o l} h {R} hR =>
    (C.Gd.sub_left (sigSub C.AU (by omega_using [h, hdAn]))).sub_right hR
  have dXk : ∀ {o l : Nat}, o + l ≤ (p.a + 1) * p.n →
      Region.Disjoint ⟨AU + BitVec.ofNat 64 o, l⟩ (below (t₀.gpr .rsp) stack) := fun {o l} h =>
    C.Gs.sub_left (sigSub C.AU (by omega_using [h, hdAn]))
  refine WP.mono (zero3_ok hbx hw) fun t₁ ⟨g₁, r₁, w₁, mx₁, v3₁, f₁⟩ => ?_
  have k₁ : ∀ q, q < 31648 → (q < 2728 ∨ 2736 ≤ q) → t₁.mem (at' S q) = t.mem (at' S q) := fun q hq h =>
    keepS f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact dS S (by rw [oVar2]; omega_using [h]) (by omega_using [hq]) (by rw [oVar2]; omega_using [])
  have dv3 : ∀ i, i < 9 → i ≠ 3 → ∀ r ∈ [(⟨at' S (Layout.oVar 2 3), 8⟩ : Region)],
      Region.Disjoint ⟨at' S (Layout.oVar 2 i), 8⟩ r := fun i hi h3 r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact dS S (by rw [oVar2, oVar2]; omega_using [h3]) (by rw [oVar2]; omega_using [hi]) (by rw [oVar2]; omega_using [])
  have hbx₁ : t₁.gpr .rbx = S := by rw [g₁ _ (by decide), hbx]
  have hsp₁ : t₁.gpr .rsp = t₀.gpr .rsp := by rw [g₁ _ (by decide), hsp]
  have hw₁ : (⟨S, 2 ^ 16⟩ : Region) ∈ t₁.wr := by rw [w₁]; exact hw
  have hfix₁ : Fix t₀ t₁ := hI.fix.trans ⟨fun r hr => g₁ r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), r₁, w₁, by rw [mx₁]⟩
  have hsig : ∀ w < p.n / 8, InRegions t₁.wr (AU + BitVec.ofNat 64 (8 * w)) 8 := fun w hw' => by
    rw [w₁, hI.fix.wr]; exact sigIn C.wG C.AU (by omega_using [hw', hdAn, han, hn]) C.Gf (by decide)
  refine ⟨hfix₁, ⟨hbx₁, hfix₁.cs _ (by simp [calleeSaved]), C.kp, by rw [hfix₁.cs _ (by simp [calleeSaved]), C.r13],
    by omega_using [C.idx, h2a], hw₁, C.fit, by rw [hsp₁]; exact C.stk,
    by have := C.tt; rw [Nat.succ_mul] at this; omega_using [this, hu1'], hsig,
    by rw [show AU = AU + BitVec.ofNat 64 0 from (BitVec.add_zero AU).symm]; exact dXs (by omega_using [han]) (fun _ h => h),
    by rw [hsp₁, show AU = AU + BitVec.ofNat 64 0 from (BitVec.add_zero AU).symm]; exact dXk (by omega_using [han])⟩,
    ⟨Fix.refl _, env_bytes hn32 hI.env fun q hq => k₁ q (by simp only [EnvB] at hq; omega_using [hq])
        (by simp only [EnvB] at hq; omega_using [hq]),
      sk_bytes hI.sk fun q h₁ h₂ => k₁ q (by omega_using [h₂, hn32]) (.inr (by omega_using [h₁])),
      by rw [keepSW f₁ (dv3 1 (by decide) (by decide)), hI.v1],
      by rw [keepSW f₁ (dv3 2 (by decide) (by decide)), hI.v2], v3₁,
      by rw [keepSW f₁ (dv3 4 (by decide) (by decide)), hI.v4],
      fun _ h => absurd h (by omega_using []), fun j _ => by rw [ite_eq_right (by omega_using [])], Frame.refl _ _⟩⟩

/-- After the leaves, in one run: what the heights need. -/
theorem sub_s2 (T : Thash4Impl p.n) (name ln : String) {stack : Nat} (hst : T.stack + 24 ≤ stack)
    (hs63 : stack < 2 ^ 63) {S SG AU : Addr} {L dA tt idx : Nat} {pkSeed a16 skSeed : List Byte} {t₀ : State}
    (C : SC p stack S SG AU L dA tt idx t₀) {u : Nat} (hu : u < 2 ^ (p.a - s p.a)) {t₁ t₂ : State}
    (hfix₁ : Fix t₀ t₁)
    (L₂ : LS p stack S AU pkSeed a16 skSeed (t₀.gpr .r12).toNat (tt * 2 ^ p.a) (u * 2 ^ s p.a) idx t₁ (2 ^ s p.a) t₂) :
    SubHH p stack S SG AU (t₀.gpr .rsp) L dA (u * 2 ^ s p.a) (tt * 2 ^ p.a) idx pkSeed a16 t₂ ∧
      WP isa (subtreeHeights ⟨p.n, p.len⟩ p.a name ln T.code) t₂ fun t₃ => t₃.gpr .rbx = S := by
  have hn := C.hn
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hs6 := s_ge C.a6
  have hsa := s_le p.a
  have has := a_s C.a14
  have h2a : 2 ^ p.a ≤ 2 ^ 14 := Nat.pow_le_pow_right (by decide) C.a14
  have hU : 2 ^ (p.a - s p.a) ≤ 32 := by
    calc 2 ^ (p.a - s p.a) ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) has
      _ = 32 := rfl
  have hUs : 2 ^ (p.a - s p.a) * 2 ^ s p.a = 2 ^ p.a := by rw [← Nat.pow_add, Nat.sub_add_cancel hsa]
  have hu1 : (u + 1) * 2 ^ s p.a ≤ 2 ^ p.a := by rw [← hUs]; exact Nat.mul_le_mul_right _ hu
  have hu1' : u * 2 ^ s p.a + 2 ^ s p.a ≤ 2 ^ p.a := by rw [← Nat.succ_mul]; exact hu1
  have hdAn : dA + (p.a + 1) * p.n ≤ L := C.dA
  have han : (p.a + 1) * p.n = p.n + p.a * p.n := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
  have hsn : s p.a * p.n ≤ p.a * p.n := Nat.mul_le_mul_right _ hsa
  have hfix₂ : Fix t₀ t₂ := hfix₁.trans L₂.fix
  have hr12₂ : t₂.gpr .r12 = t₀.gpr .r12 := hfix₂.cs _ (by simp [calleeSaved])
  have hbx₂ : t₂.gpr .rbx = S := by rw [hfix₂.cs _ (by simp [calleeSaved]), C.bx]
  have hsp₂ : t₂.gpr .rsp = t₀.gpr .rsp := hfix₂.cs _ (by simp [calleeSaved])
  have hX : tt * 2 ^ p.a + u * 2 ^ s p.a < 2 ^ 32 := by
    have := C.tt; rw [Nat.succ_mul] at this; omega_using [this, hu1']
  have hdv4 : 2 ^ s p.a ∣ tt * 2 ^ p.a := Nat.dvd_mul_left_of_dvd (Nat.pow_dvd_pow 2 hsa) _
  have hR : u * 2 ^ s p.a / 2 ^ s p.a = u := Nat.mul_div_cancel _ (Nat.two_pow_pos _)
  have h16 : a16.length = 16 := by rw [← L₂.env.adrsA 0 (by decide)]; simp [bytesAt]
  refine ⟨⟨hbx₂, by rw [hr12₂]; exact C.kp, by rw [hfix₂.cs _ (by simp [calleeSaved]), C.r13],
    by omega_using [C.idx, h2a], by rw [hfix₂.wr]; exact C.w, by rw [hfix₂.wr]; exact C.wG, C.AU,
    by omega_using [hdAn, han, hsn], C.Gf, C.fit, hsp₂, C.stk, C.Gd, C.Gs, L₂.env, L₂.v1, L₂.v2, L₂.v4, hX, hs6⟩, ?_⟩
  refine WP.mono (subHeights_ok T name ln hn C.hf hst hs63 (L := L) (dA := dA) (U2 := u * 2 ^ s p.a)
    (V4 := tt * 2 ^ p.a) (idx := idx) (pkSeed := pkSeed) (a16 := a16) (skSeed := skSeed) hbx₂
    (by rw [hr12₂]; exact C.kp) (by rw [hfix₂.cs _ (by simp [calleeSaved]), C.r13]) (by omega_using [C.idx, h2a])
    (by rw [hfix₂.wr]; exact C.w) (by rw [hfix₂.wr]; exact C.wG) C.AU (by omega_using [hdAn, han, hsn]) C.Gf C.fit
    (by rw [hsp₂]; exact C.stk) C.Gd (by rw [hsp₂]; exact C.Gs) L₂.env L₂.v1 L₂.v2 L₂.v4 hX hdv4
    (Nat.dvd_mul_left _ _) (by rw [hR]; omega_using [hu, hU]) hs6 fun i hi => by
      rw [hr12₂, L₂.nodes i hi, leafv_node h16 C.kp]) fun t₃ H => ?_
  rw [H.fix.cs _ (by simp [calleeSaved]), hbx₂]

theorem sub_ct (hp : FSet p) (T : Thash4Impl p.n) (name ln : String) {stack : Nat} (hst : T.stack + 24 ≤ stack)
    (hs63 : stack < 2 ^ 63) {S SG AU : Addr} {L dA tt idx₁ idx₂ : Nat} {pk₁ a₁ sk₁ pk₂ a₂ sk₂ : List Byte}
    {t₁ t₂ : State} (C₁ : SC p stack S SG AU L dA tt idx₁ t₁) (C₂ : SC p stack S SG AU L dA tt idx₂ t₂)
    (hsp : t₁.gpr .rsp = t₂.gpr .rsp) {u : Nat} (hu : u < 2 ^ (p.a - s p.a)) :
    RelCT isa (fun a b => ST p stack S AU pk₁ a₁ sk₁ (t₁.gpr .r12).toNat tt idx₁ t₁ u a ∧
        ST p stack S AU pk₂ a₂ sk₂ (t₂.gpr .r12).toNat tt idx₂ t₂ u b)
      (subtreeBody ⟨p.n, p.len⟩ p.a name ln T.code) fun _ _ => True := by
  have hn := C₁.hn
  have hs6 := s_ge C₁.a6
  have hd4 : 4 ∣ 2 ^ s p.a := by simpa using (Nat.pow_dvd_pow 2 (show 2 ≤ s p.a by omega_using [hs6]))
  have hm4 : 0 + 4 * (2 ^ s p.a / 4) = 2 ^ s p.a := by rw [Nat.zero_add]; exact Nat.mul_div_cancel' hd4
  have h64 : 64 ≤ 2 ^ s p.a := by
    calc 64 = 2 ^ 6 := rfl
      _ ≤ 2 ^ s p.a := Nat.pow_le_pow_right (by decide) hs6
  have hm0 : 0 < 2 ^ s p.a / 4 := by omega_using [hm4, h64]
  unfold subtreeBody
  refine Levels.relSeq (ct_zero3 fun x y ⟨hx, hy⟩ r hr => ?_) (fun x h => sub_s1 C₁ hu h) (fun x h => sub_s1 C₂ hu h) ?_
  · simp only [List.mem_singleton] at hr; subst hr
    rw [hx.fix.cs _ (by simp [calleeSaved]), hy.fix.cs _ (by simp [calleeSaved]), C₁.bx, C₂.bx]
  refine Levels.relSeq (B₁ := fun z => ∃ y, Fix t₁ y ∧
      LS p stack S AU pk₁ a₁ sk₁ (t₁.gpr .r12).toNat (tt * 2 ^ p.a) (u * 2 ^ s p.a) idx₁ y (2 ^ s p.a) z)
    (B₂ := fun z => ∃ y, Fix t₂ y ∧
      LS p stack S AU pk₂ a₂ sk₂ (t₂.gpr .r12).toNat (tt * 2 ^ p.a) (u * 2 ^ s p.a) idx₂ y (2 ^ s p.a) z) ?_
    (fun x ⟨fx, LC, L0⟩ => WP.mono (leaves_ok T name hn C₁.hf (by omega_using [hst]) hs63 LC.bx LC.r12 LC.kp LC.r13
      LC.idx LC.w LC.fit LC.stk LC.X LC.out LC.d LC.As hm0 hm4 L0) fun z h => ⟨x, fx, h⟩)
    (fun x ⟨fx, LC, L0⟩ => WP.mono (leaves_ok T name hn C₂.hf (by omega_using [hst]) hs63 LC.bx LC.r12 LC.kp LC.r13
      LC.idx LC.w LC.fit LC.stk LC.X LC.out LC.d LC.As hm0 hm4 L0) fun z h => ⟨x, fx, h⟩) ?_
  · intro x y v₁ v₂ x' y' ⟨⟨fx, LCx, L0x⟩, ⟨fy, LCy, L0y⟩⟩ e₁ e₂
    exact ⟨(leaves_ct hp T name (by omega_using [hst]) hs63 LCx LCy
      (by rw [fx.cs _ (by simp [calleeSaved]), fy.cs _ (by simp [calleeSaved]), hsp]) (2 ^ s p.a / 4) _ _ _ _ _ _
      ⟨⟨0, hm4, hm0, L0x⟩, ⟨0, hm4, hm0, L0y⟩⟩ e₁ e₂).1, trivial⟩
  refine Levels.relSeq (B₁ := fun w => w.gpr .rbx = S) (B₂ := fun w => w.gpr .rbx = S)
    (RelCT.mono (subH_ct hp T name ln hst hs63 (sp := t₁.gpr .rsp)) (fun a b ⟨⟨y, fy, La⟩, ⟨y', fy', Lb⟩⟩ =>
      ⟨(sub_s2 T name ln hst hs63 C₁ hu fy La).1, by
        have := (sub_s2 T name ln hst hs63 C₂ hu fy' Lb).1; rw [← hsp] at this; exact this⟩) fun _ _ h => h)
    (fun a ⟨y, fy, La⟩ => (sub_s2 T name ln hst hs63 C₁ hu fy La).2)
    (fun b ⟨y, fy, Lb⟩ => (sub_s2 T name ln hst hs63 C₂ hu fy Lb).2) ?_
  exact ct_next2 hp.2 fun x y ⟨hx, hy⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [hx, hy]

/-! ## The heights above the subtrees, in two runs -/

/-- `levels`'s regions above the subtrees. -/
abbrev topW (p : Params) (S AU : Addr) : List Region :=
  [⟨S, scratchLen⟩, ⟨AU + BitVec.ofNat 64 (p.n + s p.a * p.n), (p.a - s p.a) * p.n⟩]

/-- After the parameters of `levels` above the subtrees, in one run. -/
structure TopMid (p : Params) (stack : Nat) (T : Thash4Impl p.n) (name ln : String) (S AU sp : Addr) (tt : Nat)
    (u : State) : Prop where
  rdi : u.gpr .rdi = S
  rsi : u.gpr .rsi = at' S Layout.oN
  rdx : u.gpr .rdx = BitVec.ofNat 64 (2 ^ (p.a - s p.a))
  rcx : u.gpr .rcx = BitVec.ofNat 64 (s p.a)
  r8 : u.gpr .r8 = AU + BitVec.ofNat 64 (p.n + s p.a * p.n)
  rsp : u.gpr .rsp = sp
  pre : (levelsContract p (stack - 8)).pre (u.callEntry.withRegions [] (topW p S AU))
  c₁ : Covers ([] ++ topW p S AU) (u.rd ++ u.wr)
  c₂ : Covers (topW p S AU) u.wr
  call : WP isa (.call ln (Impl.SlhDsa.X86_64.Tree.levels ⟨p.n, p.len⟩ name T.code)) u fun v =>
    v.gpr .rbx = S ∧ (⟨S, 2 ^ 16⟩ : Region) ∈ v.wr ∧ v.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 tt

theorem top_mid (T : Thash4Impl p.n) (name ln : String) {stack : Nat} (hst : T.stack + 24 ≤ stack)
    (hs63 : stack < 2 ^ 63) {S SG AU : Addr} {L dA tt idx : Nat} {pkSeed a16 skSeed : List Byte} {t₀ : State}
    (C : SC p stack S SG AU L dA tt idx t₀) (hc : s p.a < p.a) {t : State}
    (hI : ST p stack S AU pkSeed a16 skSeed (t₀.gpr .r12).toNat tt idx t₀ (2 ^ (p.a - s p.a)) t)
    (h0 : t.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 tt) :
    WP isa (.block (copyWords .rbx Layout.oN .rbx Layout.oRoots
        (2 ^ (p.a - s p.a) * (⟨p.n, p.len⟩ : Layout).n / 8) ++
      ([.mov .r10 (.mem (var 1)), .alu .add .r10 (.imm (BitVec.ofNat 32 ((⟨p.n, p.len⟩ : Layout).n +
        s p.a * (⟨p.n, p.len⟩ : Layout).n)))] : List Instr) ++
      Impl.SlhDsa.X86_64.Tree.setParams (.imm 0) (.mem (var 4)) (.imm 3) (.reg .r12) ++
      ([.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 Layout.oN)),
        .mov32 .rdx (.imm (BitVec.ofNat 32 (2 ^ (p.a - s p.a)))), .mov32 .rcx (.imm (BitVec.ofNat 32 (s p.a))),
        .mov .r8 (.reg .r10), .mov .r9 (.reg .r13)] : List Instr))) t (TopMid p stack T name ln S AU (t₀.gpr .rsp) tt) := by
  have hn := C.hn
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hsa := s_le p.a
  have has := a_s C.a14
  have han : (p.a + 1) * p.n = p.n + p.a * p.n := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
  have hdAn : dA + (p.a + 1) * p.n ≤ L := C.dA
  have hbx : t.gpr .rbx = S := by rw [hI.fix.cs _ (by simp [calleeSaved]), C.bx]
  have hsp : t.gpr .rsp = t₀.gpr .rsp := hI.fix.cs _ (by simp [calleeSaved])
  have hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr := by rw [hI.fix.wr]; exact C.w
  have h2U : 2 ^ (p.a - s p.a) ≤ 32 := by
    calc 2 ^ (p.a - s p.a) ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) has
      _ = 32 := rfl
  have hUn : 2 ^ (p.a - s p.a) * p.n ≤ 1024 := by have := Nat.mul_le_mul h2U hn32; omega_using [this]
  have h8 : 8 ∣ p.n := by omega_using [hn]
  have e8 : 8 * (2 ^ (p.a - s p.a) * p.n / 8) = 2 ^ (p.a - s p.a) * p.n :=
    Nat.mul_div_cancel' (Nat.dvd_mul_left_of_dvd h8 _)
  have eN : Layout.oN = 12640 := rfl
  have eR : Layout.oRoots = 29280 := rfl
  refine WP.block_append (WP.block_append (WP.block_append
    (WP.mono_mx (by simpa [Code.allInstrs_eq, instrs] using
        (copyWords_nm .rbx Layout.oN .rbx Layout.oRoots (2 ^ (p.a - s p.a) * p.n / 8)))
      (Levels.copy_ok (S := S) (a := 0) (b := 0) (d₁ := Layout.oRoots) (d₂ := Layout.oN) (by decide) (by decide)
        (2 ^ (p.a - s p.a) * p.n / 8) t (by rw [hbx]; exact Levels.scr0 S) (by rw [hbx]; exact Levels.scr0 S) hw
        (by rw [e8, eR]; omega_using [hUn]) (by rw [e8, eN]; omega_using [hUn]) (by rw [e8, eN, eR]; omega_using [hUn]))
      fun u₁ ⟨g₁, _, w₁, _, f₁⟩ _ => ?_)))
  rw [e8, Nat.zero_add] at f₁
  have kc : ∀ q, q < 2 ^ 16 → (q < Layout.oN ∨ Layout.oN + 2 ^ (p.a - s p.a) * p.n ≤ q) →
      u₁.mem (at' S q) = t.mem (at' S q) := fun q hq h => keepS f₁ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact dS S (by omega_using [h]) (by omega_using [hq]) (by rw [eN]; omega_using [hUn])
  have kcw : ∀ i, i < 9 → u₁.mem.readW (at' S (Layout.oVar 2 i)) 64 = t.mem.readW (at' S (Layout.oVar 2 i)) 64 :=
    fun i hi => Mem.readW_congr fun j hj => by
      rw [Levels.add_add, oVar2]; exact kc _ (by omega_using [hi, hj]) (.inl (by rw [eN]; omega_using [hi, hj]))
  have hbx₁ : u₁.gpr .rbx = S := by rw [g₁ _ (by decide), hbx]
  have hw₁ : (⟨S, 2 ^ 16⟩ : Region) ∈ u₁.wr := by rw [w₁]; exact hw
  refine WP.block_append_iff.mp (WP.block_append_iff.mp (WP.mono (topB_ok hn C.a14 (V4 := tt * 2 ^ p.a) (AU := AU)
    hbx₁ hw₁ (by rw [kcw 1 (by decide), hI.v1]) (by rw [kcw 4 (by decide), hI.v4])) fun u₂ B => ?_))
  have hsp₂ : u₂.gpr .rsp = t₀.gpr .rsp := by
    rw [B.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₁ _ (by decide), hsp]
  have kB : ∀ q, q < 2 ^ 16 → (q < 3000 ∨ 3032 ≤ q) → u₂.mem (at' S q) = u₁.mem (at' S q) := fun q hq h =>
    keepS B.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact dS S (by rw [oVar4]; omega_using [h]) (by omega_using [hq]) (by rw [oVar4]; omega_using [])
  have hE₂ : Env p u₂.mem S pkSeed a16 := env_bytes hn32 (env_bytes hn32 hI.env fun q hq => kc q
    (by simp only [EnvB] at hq; omega_using [hq]) (.inl (by simp only [EnvB] at hq; rw [eN]; omega_using [hq])))
    fun q hq => kB q (by simp only [EnvB] at hq; omega_using [hq]) (by simp only [EnvB] at hq; omega_using [hq])
  have has1 : (p.a - s p.a) * p.n + s p.a * p.n = p.a * p.n := by rw [← Nat.add_mul, Nat.sub_add_cancel hsa]
  have hAU' : AU + BitVec.ofNat 64 (p.n + s p.a * p.n) = SG + BitVec.ofNat 64 (dA + (p.n + s p.a * p.n)) := by
    rw [C.AU, Levels.add_add]
  have hsubA : Region.Sub ⟨AU + BitVec.ofNat 64 (p.n + s p.a * p.n), (p.a - s p.a) * p.n⟩ ⟨SG, L⟩ := by
    rw [hAU']; exact Offset.sub_base SG (by omega_using [hdAn, han, has1])
  have ht : ∀ (x : Nat), x < 2 ^ 32 → (BitVec.ofNat 64 x).toNat = x := fun x hx => by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hx])
  have hV4 : tt * 2 ^ p.a < 2 ^ 32 := by have := C.tt; rw [Nat.succ_mul] at this; omega_using [this]
  have hva : ∀ i, varAt u₂.mem S 4 i = u₂.mem.readW (at' S (Layout.oVar 4 i)) 64 := fun _ => rfl
  have h2a : 2 ^ p.a ≤ 2 ^ 14 := Nat.pow_le_pow_right (by decide) C.a14
  have hpos : 1 ≤ (p.a - s p.a) * p.n := Nat.mul_pos (by omega_using [hc]) (by omega_using [hn])
  have hr9 : (u₂.gpr .r9).toNat < 2 ^ 32 := by
    rw [B.r9, g₁ _ (by decide), hI.fix.cs _ (by simp [calleeSaved]), C.r13, ht idx (by omega_using [C.idx, h2a])]
    omega_using [C.idx, h2a]
  have hcnt : (2 ^ (p.a - s p.a) + 8) * p.n ≤ 32 * Layout.nodeSlots := by
    rw [show Layout.nodeSlots = 520 from rfl]
    have := Nat.mul_le_mul (show 2 ^ (p.a - s p.a) + 8 ≤ 40 by omega_using [h2U]) hn32
    omega_using [this]
  have hwS : (⟨S, 2 ^ 16⟩ : Region) ∈ u₂.wr := by rw [B.wr, w₁, hI.fix.wr]; exact C.w
  have hwG : (⟨SG, L⟩ : Region) ∈ u₂.wr := by rw [B.wr, w₁, hI.fix.wr]; exact C.wG
  have hstk₂ : (below (u₂.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩ := by rw [hsp₂]; exact C.stk
  have hAf : (AU + BitVec.ofNat 64 (p.n + s p.a * p.n)).toNat + (p.a - s p.a) * p.n ≤ 2 ^ 64 := by
    rw [hAU', Levels.toNat_at (by have := C.Gf; omega_using [this, hdAn, han, has1, hpos])]
    have := C.Gf; omega_using [this, hdAn, han, has1]
  have hAs : Region.Disjoint ⟨AU + BitVec.ofNat 64 (p.n + s p.a * p.n), (p.a - s p.a) * p.n⟩
      (below (u₂.gpr .rsp) stack) := by rw [hsp₂]; exact C.Gs.sub_left hsubA
  have hvA : ∀ i, 5 ≤ i → i ≤ 8 → (varAt u₂.mem S 4 i).toNat < 2 ^ 32 := fun i h₁ h₂ => by
    rw [hva]
    rcases (show i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 by omega_using [h₁, h₂]) with rfl | rfl | rfl | rfl
    · rw [B.v5]; decide
    · rw [B.v6, ht _ hV4]; exact hV4
    · rw [B.v7]; decide
    · rw [B.v8, g₁ _ (by decide), hI.fix.cs _ (by simp [calleeSaved])]; exact C.kp
  obtain ⟨hpre, hc₁, hc₂⟩ := lcall_pre T hn hst hs63 (h := p.a - s p.a) (z₀ := s p.a) (L := L)
    (d := dA + (p.n + s p.a * p.n)) B.rdi B.rsi B.rdx B.rcx B.r8 hr9 (by omega_using [hc]) (by omega_using [hsa, C.a14])
    hcnt hwS hwG hAU' (by omega_using [hdAn, han, has1]) C.fit hstk₂ hAf (C.Gd.sub_left hsubA) hAs hE₂ hvA
  refine ⟨B.rdi, B.rsi, B.rdx, B.rcx, B.r8, hsp₂, hpre, hc₁, hc₂,
    lcall_ok T name ln hn C.hf hst hs63 (h := p.a - s p.a) (z₀ := s p.a) (L := L)
    (d := dA + (p.n + s p.a * p.n)) B.rdi B.rsi B.rdx B.rcx B.r8 hr9 (by omega_using [hc]) (by omega_using [hsa, C.a14])
    hcnt hwS hwG hAU' (by omega_using [hdAn, han, has1]) C.fit hstk₂ hAf (C.Gd.sub_left hsubA) hAs hE₂ hvA
    fun v' fx _ _ _ fr => ⟨?_, by rw [fx.wr]; exact hwS, ?_⟩⟩
  · rw [fx.cs _ (by simp [calleeSaved]), B.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), hbx₁]
  · have hcnt' : Layout.oN + (2 ^ (p.a - s p.a) + 8) * p.n ≤ 31648 := by
      rw [show Layout.nodeSlots = 520 from rfl] at hcnt; rw [eN]; omega_using [hcnt]
    rw [← h0, ← kcw 0 (by decide), oVar2]
    refine Mem.readW_congr fun j hj => ?_
    rw [Levels.add_add, ← kB (2704 + 8 * 0 + j) (by omega_using [hj]) (by omega_using [hj])]
    refine keepS fr fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · simp only [levelsChanges, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with ⟨k, hk, rfl⟩ | rfl | rfl | rfl | rfl
      · exact dS S (.inl (by rw [laneA_eq]; omega_using [hj])) (by omega_using [hj]) (by rw [laneA_eq]; omega_using [hk, hn32])
      · exact Offset.disjoint_base S (by omega_using []) (by omega_using [hj])
      · exact dS S (.inr (by omega_using [])) (by omega_using [hj]) (by decide)
      · exact dS S (.inl (by rw [show Layout.oFrame 4 = 2912 from rfl]; omega_using [hj])) (by omega_using [hj]) (by decide)
      · exact dS S (.inl (by rw [eN]; omega_using [hj])) (by omega_using [hj]) (by omega_using [hcnt'])
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dqlow (C.Gd.sub_left hsubA) (by omega_using [hj])
      · exact (hstk₂.sub_right (Levels.sub_scr S (by omega_using [hj]))).symm

theorem top_ct (hp : FSet p) (T : Thash4Impl p.n) (name ln : String) {stack : Nat} (hst : T.stack + 24 ≤ stack)
    (hs63 : stack < 2 ^ 63) {S SG AU : Addr} {L dA tt idx₁ idx₂ : Nat} {pk₁ a₁ sk₁ pk₂ a₂ sk₂ : List Byte}
    {t₁ t₂ : State} (C₁ : SC p stack S SG AU L dA tt idx₁ t₁) (C₂ : SC p stack S SG AU L dA tt idx₂ t₂)
    (hsp : t₁.gpr .rsp = t₂.gpr .rsp) :
    RelCT isa (fun a b => (ST p stack S AU pk₁ a₁ sk₁ (t₁.gpr .r12).toNat tt idx₁ t₁ (2 ^ (p.a - s p.a)) a ∧
        a.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 tt) ∧
        (ST p stack S AU pk₂ a₂ sk₂ (t₂.gpr .r12).toNat tt idx₂ t₂ (2 ^ (p.a - s p.a)) b ∧
        b.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 tt))
      (topHeights ⟨p.n, p.len⟩ p.a name ln T.code) fun _ _ => True := by
  obtain ⟨hf, hn, -, -, -, -, -, -⟩ := hp.facts
  have hp6 : P6 p := hp.2
  have hB : ∀ {t₀ : State} {idx pk a sk} {C : SC p stack S SG AU L dA tt idx t₀} (x : State),
      (ST p stack S AU pk a sk (t₀.gpr .r12).toNat tt idx t₀ (2 ^ (p.a - s p.a)) x ∧
        x.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 tt) →
      x.gpr .rbx = S ∧ (⟨S, 2 ^ 16⟩ : Region) ∈ x.wr ∧
        x.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 tt := fun {t₀ idx pk a sk C} x ⟨H, h0⟩ =>
    ⟨by rw [H.fix.cs _ (by simp [calleeSaved]), C.bx], by rw [H.fix.wr]; exact C.w, h0⟩
  unfold topHeights
  by_cases hc : s p.a < p.a
  · rw [ite_eq_left hc]
    refine Levels.relSeq (B₁ := fun v => v.gpr .rbx = S ∧ (⟨S, 2 ^ 16⟩ : Region) ∈ v.wr ∧
        v.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 tt) (B₂ := fun v => v.gpr .rbx = S ∧
        (⟨S, 2 ^ 16⟩ : Region) ∈ v.wr ∧ v.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 tt) ?_
      (fun x ⟨H, h0⟩ => WP.seq (WP.mono (top_mid T name ln hst hs63 C₁ hc H h0) fun u M => M.call))
      (fun x ⟨H, h0⟩ => WP.seq (WP.mono (top_mid T name ln hst hs63 C₂ hc H h0) fun u M => M.call))
      (load_ct .rdx (by decide) (by decide) (fun v h => h) (fun v h => h) (ct_rootB hp6))
    refine Levels.relSeq (ct_topB hp6 fun x y ⟨hx, hy⟩ r hr => ?_) (fun x ⟨H, h0⟩ => top_mid T name ln hst hs63 C₁ hc H h0)
      (fun x ⟨H, h0⟩ => top_mid T name ln hst hs63 C₂ hc H h0) ?_
    · simp only [List.mem_singleton] at hr; subst hr
      rw [(hB (C := C₁) x hx).1, (hB (C := C₂) y hy).1]
    refine RelCT.call (Levels.levels_correct T name hn hf (stack := stack - 8) (by omega_using [hst]) (by omega_using [hs63]))
      (Levels.levels_ct T name hn hf (by omega_using [hst]) (by omega_using [hs63])) [] (topW p S AU)
      fun x y ⟨hx, hy⟩ => ⟨hx.pre, hy.pre, lpub (by rw [hx.rdi, hy.rdi]) (by rw [hx.rsi, hy.rsi]) (by rw [hx.rdx, hy.rdx])
        (by rw [hx.rcx, hy.rcx]) (by rw [hx.r8, hy.r8]) (by rw [hx.rsp, hy.rsp, hsp]), hx.c₁, hx.c₂, hy.c₁, hy.c₂,
        by rw [hx.rsp, hy.rsp, hsp]⟩
  · rw [ite_eq_right hc]
    exact Levels.relSeq ct_nil (fun x h => WP.block_nil (hB (C := C₁) x h)) (fun x h => WP.block_nil (hB (C := C₂) x h))
      (load_ct .rdx (by decide) (by decide) (fun v h => h) (fun v h => h) (ct_rootB hp6))

/-! ## The loop of subtrees, in two runs -/

abbrev SI (p : Params) (stack : Nat) (S AU : Addr) (pkSeed a16 skSeed : List Byte) (kp tt idx : Nat) (t₀ : State)
    (m : Nat) (v : State) : Prop :=
  ∃ u, u + m = 2 ^ (p.a - s p.a) ∧ 0 < m ∧ ST p stack S AU pkSeed a16 skSeed kp tt idx t₀ u v

theorem subs_step (T : Thash4Impl p.n) (name ln : String) {stack : Nat} (hst : T.stack + 24 ≤ stack)
    (hs63 : stack < 2 ^ 63) {S SG AU : Addr} {L dA tt idx : Nat} {pkSeed a16 skSeed : List Byte} {t₀ : State}
    (C : SC p stack S SG AU L dA tt idx t₀) (m : Nat) (v : State)
    (hI : SI p stack S AU pkSeed a16 skSeed (t₀.gpr .r12).toNat tt idx t₀ m v) :
    WP isa (subtreeBody ⟨p.n, p.len⟩ p.a name ln T.code) v fun v' => isa.eval .ne v' = some (decide (1 < m)) ∧
      (decide (1 < m) = false → ST p stack S AU pkSeed a16 skSeed (t₀.gpr .r12).toNat tt idx t₀ (2 ^ (p.a - s p.a)) v') ∧
      (decide (1 < m) = true → m - 1 < m ∧ SI p stack S AU pkSeed a16 skSeed (t₀.gpr .r12).toNat tt idx t₀ (m - 1) v') := by
  obtain ⟨u, hu, hm, H⟩ := hI
  have hUs : 2 ^ (p.a - s p.a) * 2 ^ s p.a = 2 ^ p.a := by rw [← Nat.pow_add, Nat.sub_add_cancel (s_le p.a)]
  refine WP.mono (sub_ok T name ln hst hs63 C (by omega_using [hu, hm]) H) fun v' ⟨hz, H'⟩ => ?_
  have hiff : (u + 1) * 2 ^ s p.a = 2 ^ p.a ↔ ¬ 1 < m := by
    rw [← hUs]
    constructor
    · intro e; have := Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) e; omega_using [this, hu]
    · intro e; rw [show u + 1 = 2 ^ (p.a - s p.a) by omega_using [e, hu, hm]]
  refine ⟨by rw [eval_ne hz]; congr 1; by_cases h : 1 < m <;> simp [h, hiff], fun hc => ?_, fun hc => ?_⟩
  · have := of_decide_eq_false hc
    rw [show 2 ^ (p.a - s p.a) = u + 1 by omega_using [this, hu, hm]]; exact H'
  · have := of_decide_eq_true hc
    exact ⟨by omega_using [this], u + 1, by omega_using [hu, this], by omega_using [this], H'⟩

theorem subs_ct (hp : FSet p) (T : Thash4Impl p.n) (name ln : String) {stack : Nat} (hst : T.stack + 24 ≤ stack)
    (hs63 : stack < 2 ^ 63) {S SG AU : Addr} {L dA tt idx₁ idx₂ : Nat} {pk₁ a₁ sk₁ pk₂ a₂ sk₂ : List Byte}
    {t₁ t₂ : State} (C₁ : SC p stack S SG AU L dA tt idx₁ t₁) (C₂ : SC p stack S SG AU L dA tt idx₂ t₂)
    (hsp : t₁.gpr .rsp = t₂.gpr .rsp) (m : Nat) :
    RelCT isa (fun a b => SI p stack S AU pk₁ a₁ sk₁ (t₁.gpr .r12).toNat tt idx₁ t₁ m a ∧
        SI p stack S AU pk₂ a₂ sk₂ (t₂.gpr .r12).toNat tt idx₂ t₂ m b)
      (.loop (subtreeBody ⟨p.n, p.len⟩ p.a name ln T.code) .ne) fun a b =>
        ST p stack S AU pk₁ a₁ sk₁ (t₁.gpr .r12).toNat tt idx₁ t₁ (2 ^ (p.a - s p.a)) a ∧
        ST p stack S AU pk₂ a₂ sk₂ (t₂.gpr .r12).toNat tt idx₂ t₂ (2 ^ (p.a - s p.a)) b :=
  Levels.relLoop (fun m => decide (1 < m)) (fun m => m - 1)
    (fun m => by
      intro x y v₁ v₂ x' y' ⟨⟨u, hu, hm, H₁⟩, ⟨u', hu', _, H₂⟩⟩ e₁ e₂
      obtain rfl : u = u' := by omega_using [hu, hu']
      exact sub_ct hp T name ln hst hs63 C₁ C₂ hsp (u := u) (by omega_using [hu, hm]) _ _ _ _ _ _ ⟨H₁, H₂⟩ e₁ e₂)
    (subs_step T name ln hst hs63 C₁) (subs_step T name ln hst hs63 C₂) m

/-! ## A tree, in two runs -/

/-- The first block of a tree in two runs: `rax` the tree, then `rsi` its signature. -/
theorem b1_ct (hp : P6 p) {S AU : Addr} {tt : Nat} (htt : tt < 40) {A₁ A₂ : State → Prop}
    (h₁ : ∀ a, A₁ a → a.gpr .rbx = S ∧ (⟨S, 2 ^ 16⟩ : Region) ∈ a.wr ∧
      a.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 tt ∧ a.mem.readW (at' S (Layout.oVar 2 1)) 64 = AU)
    (h₂ : ∀ a, A₂ a → a.gpr .rbx = S ∧ (⟨S, 2 ^ 16⟩ : Region) ∈ a.wr ∧
      a.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 tt ∧ a.mem.readW (at' S (Layout.oVar 2 1)) 64 = AU) :
    RelCT isa (fun a b => A₁ a ∧ A₂ b) (.block (([.mov .rax (.mem (var 0)), .mov .r13 (.mem fidx), .mov .rsi (.mem (var 1)),
      .mov32 .rax (.imm 0)] : List Instr) ++ (List.range ((p.a + 1) * (⟨p.n, p.len⟩ : Layout).n / 8)).map
        (fun w => .store (Impl.Sha3.X86_64.at_ .rsi (8 * w)) .rax) ++ ([.store (var 2) .rax] : List Instr)))
      fun _ _ => True := by
  let B : State → Prop := fun x => x.gpr .rbx = S ∧ (⟨S, 2 ^ 16⟩ : Region) ∈ x.wr ∧ x.gpr .rax = BitVec.ofNat 64 tt ∧
    x.mem.readW (at' S (Layout.oVar 2 1)) 64 = AU
  have w₁ : ∀ (A : State → Prop), (∀ a, A a → a.gpr .rbx = S ∧ (⟨S, 2 ^ 16⟩ : Region) ∈ a.wr ∧
      a.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 tt ∧ a.mem.readW (at' S (Layout.oVar 2 1)) 64 = AU) →
      ∀ a, A a → WP isa (.block [.mov .rax (.mem (var 0))]) a B := fun A h a ha =>
    Proof.Sha3.X86_64.wp_movm (a := at' S (Layout.oVar 2 0)) (by rw [var, Proof.Sha3.X86_64.ea_at, (h a ha).1])
      (Levels.in_scr' (h a ha).2.1 (by rw [oVar2]; omega_using [])) fun x e => WP.block_nil
        ⟨by rw [e.other _ (by decide), (h a ha).1], by rw [e.wr]; exact (h a ha).2.1, by rw [e.gpr, (h a ha).2.2.1],
          by rw [e.mem]; exact (h a ha).2.2.2⟩
  have w₂ : ∀ x, B x → WP isa (.block [.mov .r13 (.mem fidx), .mov .rsi (.mem (var 1))]) x
      fun y => y.gpr .rbx = S ∧ y.gpr .rsi = AU := fun x ⟨hb, hw, ha, hv⟩ =>
    Proof.Sha3.X86_64.wp_movm (a := at' S (Layout.oFidx + 8 * tt)) (ea_fidx x hb ha)
      (Levels.in_scr' hw (by rw [show Layout.oFidx = 31328 from rfl]; omega_using [htt])) fun y e =>
    Proof.Sha3.X86_64.wp_movm (a := at' S (Layout.oVar 2 1)) (by rw [var, Proof.Sha3.X86_64.ea_at, e.other _ (by decide), hb])
      (by rw [e.rd, e.wr]; exact Levels.in_scr' hw (by rw [oVar2]; omega_using [])) fun z e' => WP.block_nil
        ⟨by rw [e'.other _ (by decide), e.other _ (by decide), hb], by rw [e'.gpr, e.mem, hv]⟩
  refine RelCT.block_append (l₁ := ([.mov .rax (.mem (var 0))] : List Instr)) (Levels.relSeq (B₁ := B) (B₂ := B)
    (ct_load .rax 0 fun x y ⟨hx, hy⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(h₁ x hx).1, (h₂ y hy).1]) (w₁ A₁ h₁) (w₁ A₂ h₂) ?_)
  refine RelCT.block_append (l₁ := ([.mov .r13 (.mem fidx), .mov .rsi (.mem (var 1))] : List Instr)) (Levels.relSeq
    (ct_fidx fun x y ⟨hx, hy⟩ r hr => ?_) w₂ w₂ (ct_zeroSig hp fun x y ⟨hx, hy⟩ r hr => ?_))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hx.1, hy.1]
    · rw [hx.2, hy.2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hx.1, hy.1]
    · rw [hx.2.2.1, hy.2.2.1]

/-- The tree's signature. -/
abbrev tAU (p : Params) (SG : Addr) (tt : Nat) : Addr := SG + BitVec.ofNat 64 (tt * ((p.a + 1) * p.n))

/-- After the first block of a tree, in one run: the loop of subtrees' entry. -/
structure TreeA (p : Params) (stack : Nat) (S SG : Addr) (pkSeed a16 skSeed : List Byte) (ix : Nat → Nat)
    (t₀ : State) (tt : Nat) (t t₁ : State) : Prop where
  C : SC p stack S SG (tAU p SG tt) (p.k * ((p.a + 1) * p.n)) (tt * ((p.a + 1) * p.n)) tt (ix tt) t₁
  st : ST p stack S (tAU p SG tt) pkSeed a16 skSeed (t₁.gpr .r12).toNat tt (ix tt) t₁ 0 t₁
  v0 : t₁.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 tt
  sp : t₁.gpr .rsp = t₀.gpr .rsp

theorem tree_s1 {stack : Nat} {S SG : Addr} {pkSeed a16 skSeed : List Byte} {ix : Nat → Nat} {t₀ : State}
    (M : MC p stack S SG t₀) (hix : ∀ i < p.k, ix i < 2 ^ p.a) {tt : Nat} (htt : tt < p.k) {t : State}
    (hI : TL p stack S SG pkSeed a16 skSeed ix t₀ tt t) :
    WP isa (.block (([.mov .rax (.mem (var 0)), .mov .r13 (.mem fidx), .mov .rsi (.mem (var 1)), .mov32 .rax (.imm 0)] :
        List Instr) ++ (List.range ((p.a + 1) * (⟨p.n, p.len⟩ : Layout).n / 8)).map
          (fun w => .store (Impl.Sha3.X86_64.at_ .rsi (8 * w)) .rax) ++ ([.store (var 2) .rax] : List Instr))) t
      (TreeA p stack S SG pkSeed a16 skSeed ix t₀ tt t) := by
  have hn := M.hn
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hn8 : p.n % 8 = 0 := by omega_using [hn]
  have hkt : (tt + 1) * ((p.a + 1) * p.n) ≤ p.k * ((p.a + 1) * p.n) := Nat.mul_le_mul_right _ htt
  have hkt' : (tt + 1) * ((p.a + 1) * p.n) = tt * ((p.a + 1) * p.n) + (p.a + 1) * p.n := Nat.succ_mul _ _
  have hbx : t.gpr .rbx = S := by rw [hI.cs _ (by simp [calleeSaved]) (by decide), M.bx]
  have hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr := by rw [hI.wr]; exact M.w
  have hwG : (⟨SG, p.k * ((p.a + 1) * p.n)⟩ : Region) ∈ t.wr := by rw [hI.wr]; exact M.wG
  have h2a : 2 ^ p.a ≤ 2 ^ 14 := Nat.pow_le_pow_right (by decide) M.a14
  have htt2 : (tt + 1) * 2 ^ p.a < 2 ^ 32 := by
    have := Nat.mul_le_mul (show tt + 1 ≤ 35 by omega_using [htt, M.k35]) h2a; omega_using [this]
  refine WP.mono (treeA_ok (p := p) (S := S) (SG := SG) (L := p.k * ((p.a + 1) * p.n))
    (dA := tt * ((p.a + 1) * p.n)) (tt := tt) (idx := ix tt) hbx hw hwG rfl (by omega_using [hkt, hkt']) M.Gf hn8 hI.v0
    (by omega_using [htt, M.k35]) hI.v1 (hI.fidx tt htt) M.Gd) fun t₁ ⟨g₁, r13₁, r₁, w₁, mx₁, z₁, v2₁, f₁⟩ => ?_
  have hsubA : Region.Sub ⟨SG + BitVec.ofNat 64 (tt * ((p.a + 1) * p.n)), (p.a + 1) * p.n⟩
      ⟨SG, p.k * ((p.a + 1) * p.n)⟩ := Offset.sub_base SG (by omega_using [hkt, hkt'])
  have kA : ∀ q, q < 31648 → (q < 2720 ∨ 2728 ≤ q) → t₁.mem (at' S q) = t.mem (at' S q) := fun q hq h =>
    keepS f₁ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ((M.Gd.sub_left hsubA).sub_right (Offset.sub_base S (by
          rw [show Layout.oSigTmp = 31648 from rfl]; omega_using [hq]))).symm
      · exact dS S (by rw [oVar2]; omega_using [h]) (by omega_using [hq]) (by rw [oVar2]; omega_using [])
  have kAw : ∀ i, i < 9 → i ≠ 2 → t₁.mem.readW (at' S (Layout.oVar 2 i)) 64 = t.mem.readW (at' S (Layout.oVar 2 i)) 64 :=
    fun i hi h2 => Mem.readW_congr fun j hj => by
      rw [Levels.add_add, oVar2]; exact kA _ (by omega_using [hi, hj]) (by omega_using [hi, hj, h2])
  have hcs₁ : ∀ r ∈ calleeSaved, r ≠ .r13 → t₁.gpr r = t₀.gpr r := fun r hr h13 => by
    obtain ⟨h0, _, _, h3, _⟩ := mem_cs hr
    rw [g₁ _ h0 h13 h3, hI.cs r hr h13]
  have hE₁ : Env p t₁.mem S pkSeed a16 := env_bytes hn32 hI.env fun q hq => kA q
    (by simp only [EnvB] at hq; omega_using [hq]) (by simp only [EnvB] at hq; omega_using [hq])
  have hsk₁ : SkAt p t₁.mem S skSeed := sk_bytes hI.sk fun q h₁ h₂ => kA q (by omega_using [h₂, hn32]) (.inr (by omega_using [h₁]))
  have hz : ∀ o, o + p.n ≤ (p.a + 1) * p.n →
      bytesAt t₁.mem (SG + BitVec.ofNat 64 (tt * ((p.a + 1) * p.n)) + BitVec.ofNat 64 o) p.n = toByte 0 p.n := fun o ho =>
    bytesAt_eq_of (by simp [toByte]) fun i hi => by
      rw [Levels.add_add, z₁ _ (by omega_using [ho, hi]), toByte_zero]; simp [hi]
  refine ⟨⟨M.hf, hn, M.a6, M.a14, by rw [hcs₁ _ (by simp [calleeSaved]) (by decide), M.bx],
      by rw [hcs₁ _ (by simp [calleeSaved]) (by decide)]; exact M.kp, r13₁, hix tt htt,
      by rw [w₁]; exact hw, by rw [w₁]; exact hwG, rfl, by omega_using [hkt, hkt'], M.Gf, M.fit,
      by rw [hcs₁ _ (by simp [calleeSaved]) (by decide)]; exact M.stk, M.Gd,
      by rw [hcs₁ _ (by simp [calleeSaved]) (by decide)]; exact M.Gs, htt2⟩,
    ⟨Fix.refl _, hE₁, hsk₁, by rw [kAw 1 (by decide) (by decide), hI.v1], by rw [v2₁, Nat.zero_mul],
      by rw [kAw 4 (by decide) (by decide), hI.v4], fun j hj => by
        have := Nat.le_mul_of_pos_left p.n (show 0 < p.a + 1 by omega_using [])
        rw [ite_eq_right (by omega_using []), z₁ j (by omega_using [hj, this])],
      fun r hr => by
        rw [acc_zero, Levels.add_add (SG + BitVec.ofNat 64 (tt * ((p.a + 1) * p.n))), hz _ (by
          have := Nat.mul_le_mul_right p.n (show r + 1 ≤ p.a by omega_using [hr, s_le p.a]); rw [Nat.succ_mul] at this
          rw [Nat.add_mul, Nat.one_mul]; omega_using [this])],
      fun r _ h₂ => by
        rw [Levels.add_add (SG + BitVec.ofNat 64 (tt * ((p.a + 1) * p.n))), hz _ (by
          have := Nat.mul_le_mul_right p.n (show r + 1 ≤ p.a by omega_using [h₂]); rw [Nat.succ_mul] at this
          rw [Nat.add_mul, Nat.one_mul]; omega_using [this])],
      fun _ h => absurd h (by omega_using []), Frame.refl _ _⟩,
    by rw [kAw 0 (by decide) (by decide), hI.v0], hcs₁ _ (by simp [calleeSaved]) (by decide)⟩

/-- After the subtrees, in one run: variable 0 is still the tree. -/
theorem tree_s2 {stack : Nat} {S SG : Addr} {pkSeed a16 skSeed : List Byte} {ix : Nat → Nat} {t₀ : State}
    (M : MC p stack S SG t₀) {tt : Nat} (htt : tt < p.k) {t t₁ t₂ : State}
    (A : TreeA p stack S SG pkSeed a16 skSeed ix t₀ tt t t₁)
    (S₂ : ST p stack S (tAU p SG tt) pkSeed a16 skSeed (t₁.gpr .r12).toNat tt (ix tt) t₁ (2 ^ (p.a - s p.a)) t₂) :
    t₂.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 tt := by
  have hn32 : p.n ≤ 32 := by omega_using [M.hn]
  have hkt : (tt + 1) * ((p.a + 1) * p.n) ≤ p.k * ((p.a + 1) * p.n) := Nat.mul_le_mul_right _ htt
  have hkt' : (tt + 1) * ((p.a + 1) * p.n) = tt * ((p.a + 1) * p.n) + (p.a + 1) * p.n := Nat.succ_mul _ _
  have hsubA : Region.Sub ⟨SG + BitVec.ofNat 64 (tt * ((p.a + 1) * p.n)), (p.a + 1) * p.n⟩
      ⟨SG, p.k * ((p.a + 1) * p.n)⟩ := Offset.sub_base SG (by omega_using [hkt, hkt'])
  rw [← A.v0]
  exact keepSW S₂.frame fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map, List.mem_range] at hr
    rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨k, hk, rfl⟩
    · exact Offset.disjoint_base S (by rw [oVar2]; omega_using []) (by rw [oVar2]; omega_using [])
    · exact dS S (by rw [oVar2]; omega_using []) (by rw [oVar2]; omega_using []) (by decide)
    · exact dS S (by rw [oVar2, oVar2]; omega_using []) (by rw [oVar2]; omega_using []) (by rw [oVar2]; omega_using [])
    · exact dS S (by rw [oVar2]; decide) (by rw [oVar2]; omega_using []) (by decide)
    · exact dS S (by rw [oVar2]; decide) (by rw [oVar2]; omega_using []) (by decide)
    · exact dS S (by rw [oVar2]; decide) (by rw [oVar2]; omega_using []) (by decide)
    · exact ((M.Gd.sub_left hsubA).sub_right (Offset.sub_base S (by
        rw [oVar2, show Layout.oSigTmp = 31648 from rfl]; omega_using []))).symm
    · rw [A.sp]
      exact (M.stk.sub_right (Levels.sub_scr S (by rw [oVar2]; omega_using []))).symm
    · exact dS S (by rw [oVar2, laneA_eq]; omega_using []) (by rw [oVar2]; omega_using [])
        (by rw [laneA_eq]; omega_using [hk, hn32])

theorem tree_ct (hp : FSet p) (T : Thash4Impl p.n) (name ln : String) {stack : Nat} (hst : T.stack + 24 ≤ stack)
    (hs63 : stack < 2 ^ 63) {S SG : Addr} {pk₁ a₁ sk₁ pk₂ a₂ sk₂ : List Byte} {ix₁ ix₂ : Nat → Nat}
    {t₁ t₂ : State} (M₁ : MC p stack S SG t₁) (M₂ : MC p stack S SG t₂) (hix₁ : ∀ i < p.k, ix₁ i < 2 ^ p.a)
    (hix₂ : ∀ i < p.k, ix₂ i < 2 ^ p.a) (hsp : t₁.gpr .rsp = t₂.gpr .rsp) {tt : Nat} (htt : tt < p.k) :
    RelCT isa (fun a b => TL p stack S SG pk₁ a₁ sk₁ ix₁ t₁ tt a ∧ TL p stack S SG pk₂ a₂ sk₂ ix₂ t₂ tt b)
      (treeBody ⟨p.n, p.len⟩ p.a p.k name ln T.code) fun _ _ => True := by
  have hp6 : P6 p := hp.2
  have hn32 : p.n ≤ 32 := by omega_using [M₁.hn]
  have htk : (tt + 1) * p.n ≤ 1120 := by
    have := Nat.mul_le_mul (show tt + 1 ≤ 35 by omega_using [htt, M₁.k35]) hn32; omega_using [this]
  have hU0 : 0 < 2 ^ (p.a - s p.a) := Nat.two_pow_pos _
  have hb : ∀ {pk a sk : List Byte} {ix : Nat → Nat} {t₀ : State}, MC p stack S SG t₀ → ∀ x,
      TL p stack S SG pk a sk ix t₀ tt x → x.gpr .rbx = S ∧ (⟨S, 2 ^ 16⟩ : Region) ∈ x.wr ∧
        x.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 tt ∧
        x.mem.readW (at' S (Layout.oVar 2 1)) 64 = tAU p SG tt := fun M x H =>
    ⟨by rw [H.cs _ (by simp [calleeSaved]) (by decide), M.bx], by rw [H.wr]; exact M.w, H.v0, H.v1⟩
  unfold treeBody
  refine Levels.relSeq (B₁ := fun y => ∃ x, TreeA p stack S SG pk₁ a₁ sk₁ ix₁ t₁ tt x y)
    (B₂ := fun y => ∃ x, TreeA p stack S SG pk₂ a₂ sk₂ ix₂ t₂ tt x y)
    (b1_ct hp6 (by omega_using [htt, M₁.k35]) (hb M₁) (hb M₂))
    (fun x h => WP.mono (tree_s1 M₁ hix₁ htt h) fun y A => ⟨x, A⟩)
    (fun x h => WP.mono (tree_s1 M₂ hix₂ htt h) fun y A => ⟨x, A⟩) ?_
  refine Levels.relSeq (B₁ := fun z => ∃ x y, TreeA p stack S SG pk₁ a₁ sk₁ ix₁ t₁ tt x y ∧
      ST p stack S (tAU p SG tt) pk₁ a₁ sk₁ (y.gpr .r12).toNat tt (ix₁ tt) y (2 ^ (p.a - s p.a)) z)
    (B₂ := fun z => ∃ x y, TreeA p stack S SG pk₂ a₂ sk₂ ix₂ t₂ tt x y ∧
      ST p stack S (tAU p SG tt) pk₂ a₂ sk₂ (y.gpr .r12).toNat tt (ix₂ tt) y (2 ^ (p.a - s p.a)) z) ?_
    (fun y ⟨x, A⟩ => WP.mono (subs_ok T name ln hst hs63 A.C (u := 0) hU0 (by omega_using []) A.st)
      fun z h => ⟨x, y, A, h⟩)
    (fun y ⟨x, A⟩ => WP.mono (subs_ok T name ln hst hs63 A.C (u := 0) hU0 (by omega_using []) A.st)
      fun z h => ⟨x, y, A, h⟩) ?_
  · intro x y v₁ v₂ x' y' ⟨⟨_, A₁⟩, ⟨_, A₂⟩⟩ e₁ e₂
    exact ⟨(subs_ct hp T name ln hst hs63 A₁.C A₂.C (by rw [A₁.sp, A₂.sp, hsp]) (2 ^ (p.a - s p.a)) _ _ _ _ _ _
      ⟨⟨0, by omega_using [], hU0, A₁.st⟩, ⟨0, by omega_using [], hU0, A₂.st⟩⟩ e₁ e₂).1, trivial⟩
  refine Levels.relSeq (B₁ := fun w => w.gpr .rbx = S) (B₂ := fun w => w.gpr .rbx = S) ?_
    (fun z ⟨x, y, A, S₂⟩ => WP.mono (top_ok T name ln hst hs63 A.C htk S₂ (tree_s2 M₁ htt A S₂)) fun w P => by
      rw [P.fix.cs _ (by simp [calleeSaved]), A.C.bx])
    (fun z ⟨x, y, A, S₂⟩ => WP.mono (top_ok T name ln hst hs63 A.C htk S₂ (tree_s2 M₂ htt A S₂)) fun w P => by
      rw [P.fix.cs _ (by simp [calleeSaved]), A.C.bx])
    (ct_treeEnd hp6 fun x y ⟨hx, hy⟩ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [hx, hy])
  intro x y v₁ v₂ x' y' ⟨⟨_, _, A₁, S₁⟩, ⟨_, _, A₂, S₂⟩⟩ e₁ e₂
  exact ⟨(top_ct hp T name ln hst hs63 A₁.C A₂.C (by rw [A₁.sp, A₂.sp, hsp]) _ _ _ _ _ _
    ⟨⟨S₁, tree_s2 M₁ htt A₁ S₁⟩, ⟨S₂, tree_s2 M₂ htt A₂ S₂⟩⟩ e₁ e₂).1, trivial⟩

/-! ## The loop of trees, in two runs -/

abbrev TI (p : Params) (stack : Nat) (S SG : Addr) (pkSeed a16 skSeed : List Byte) (ix : Nat → Nat) (t₀ : State)
    (m : Nat) (v : State) : Prop :=
  ∃ tt, tt + m = p.k ∧ 0 < m ∧ TL p stack S SG pkSeed a16 skSeed ix t₀ tt v

theorem trees_step (T : Thash4Impl p.n) (name ln : String) {stack : Nat} (hst : T.stack + 24 ≤ stack)
    (hs63 : stack < 2 ^ 63) {S SG : Addr} {pkSeed a16 skSeed : List Byte} {ix : Nat → Nat} {t₀ : State}
    (M : MC p stack S SG t₀) (hix : ∀ i < p.k, ix i < 2 ^ p.a) (m : Nat) (v : State)
    (hI : TI p stack S SG pkSeed a16 skSeed ix t₀ m v) :
    WP isa (treeBody ⟨p.n, p.len⟩ p.a p.k name ln T.code) v fun v' => isa.eval .ne v' = some (decide (1 < m)) ∧
      (decide (1 < m) = false → TL p stack S SG pkSeed a16 skSeed ix t₀ p.k v') ∧
      (decide (1 < m) = true → m - 1 < m ∧ TI p stack S SG pkSeed a16 skSeed ix t₀ (m - 1) v') := by
  obtain ⟨tt, ht, hm, H⟩ := hI
  refine WP.mono (tree_ok T name ln hst hs63 M hix (by omega_using [ht, hm]) H) fun v' ⟨hz, H'⟩ => ?_
  refine ⟨by rw [eval_ne hz]; congr 1; by_cases h : 1 < m <;> simp [h] <;> omega_using [h, ht, hm], fun hc => ?_, fun hc => ?_⟩
  · have := of_decide_eq_false hc
    rw [show p.k = tt + 1 by omega_using [this, ht, hm]]; exact H'
  · have := of_decide_eq_true hc
    exact ⟨by omega_using [this], tt + 1, by omega_using [ht, this], by omega_using [this], H'⟩

theorem trees_ct (hp : FSet p) (T : Thash4Impl p.n) (name ln : String) {stack : Nat} (hst : T.stack + 24 ≤ stack)
    (hs63 : stack < 2 ^ 63) {S SG : Addr} {pk₁ a₁ sk₁ pk₂ a₂ sk₂ : List Byte} {ix₁ ix₂ : Nat → Nat}
    {t₁ t₂ : State} (M₁ : MC p stack S SG t₁) (M₂ : MC p stack S SG t₂) (hix₁ : ∀ i < p.k, ix₁ i < 2 ^ p.a)
    (hix₂ : ∀ i < p.k, ix₂ i < 2 ^ p.a) (hsp : t₁.gpr .rsp = t₂.gpr .rsp) (m : Nat) :
    RelCT isa (fun a b => TI p stack S SG pk₁ a₁ sk₁ ix₁ t₁ m a ∧ TI p stack S SG pk₂ a₂ sk₂ ix₂ t₂ m b)
      (.loop (treeBody ⟨p.n, p.len⟩ p.a p.k name ln T.code) .ne) fun a b =>
        TL p stack S SG pk₁ a₁ sk₁ ix₁ t₁ p.k a ∧ TL p stack S SG pk₂ a₂ sk₂ ix₂ t₂ p.k b :=
  Levels.relLoop (fun m => decide (1 < m)) (fun m => m - 1)
    (fun m => by
      intro x y v₁ v₂ x' y' ⟨⟨tt, ht, hm, H₁⟩, ⟨tt', ht', _, H₂⟩⟩ e₁ e₂
      obtain rfl : tt = tt' := by omega_using [ht, ht']
      exact tree_ct hp T name ln hst hs63 M₁ M₂ hix₁ hix₂ hsp (by omega_using [ht, hm]) _ _ _ _ _ _ ⟨H₁, H₂⟩ e₁ e₂)
    (trees_step T name ln hst hs63 M₁ hix₁) (trees_step T name ln hst hs63 M₂ hix₂) m

/-! ## `T_k`, in two runs -/

/-- What `pkFors` needs of the state before it, in one run. -/
structure PkH (p : Params) (stack : Nat) (S sp : Addr) (pkSeed a16 : List Byte) (t : State) : Prop where
  bx : t.gpr .rbx = S
  kp : (t.gpr .r12).toNat < 2 ^ 32
  r15 : t.gpr .r15 = at' S Layout.oMsg
  w : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr
  fit : S.toNat + 2 ^ 16 ≤ 2 ^ 64
  rsp : t.gpr .rsp = sp
  stk : (below sp stack).Disjoint ⟨S, 2 ^ 16⟩
  env : Env p t.mem S pkSeed a16

theorem pk_ct (hp : FSet p) (T : Thash4Impl p.n) (name : String) {stack : Nat} (hst : T.stack + 8 ≤ stack)
    (hs63 : stack < 2 ^ 63) {S sp : Addr} {pk₁ a₁ pk₂ a₂ : List Byte} :
    RelCT isa (fun a b => PkH p stack S sp pk₁ a₁ a ∧ PkH p stack S sp pk₂ a₂ b)
      (pkFors ⟨p.n, p.len⟩ p.k name T.code) fun _ _ => True := by
  obtain ⟨-, hn, -, -, -, hk35, -, -⟩ := hp.facts
  have hp6 : P6 p := hp.2
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hn8 : p.n % 8 = 0 := by omega_using [hn]
  have hkn : p.k * p.n ≤ 35 * 32 := Nat.mul_le_mul hk35 hn32
  have hkn8 : p.k * p.n % 8 = 0 := by rw [Nat.mul_mod, hn8, Nat.mul_zero]
  let B : State → Prop := fun y => y.gpr .rbx = S ∧ y.gpr .r15 = at' S Layout.oMsg ∧ Levels.T4Ok S stack y ∧
    y.gpr .rsp = sp
  have sF : ∀ {pk a : List Byte} (x : State), PkH p stack S sp pk a x →
      WP isa (.block (setField .rbx (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).adrsOff + 16) 4 ++
        setFieldR .rbx (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).adrsOff + 20) .r12 ++
        setField .rbx (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).adrsOff + 24) 0 ++
        setField .rbx (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).adrsOff + 28) 0)) x B := fun x H =>
    WP.mono (pkFields_ok hn H.bx H.kp H.w) fun y ⟨g, _, w, _, _, f⟩ =>
      ⟨by rw [g _ (by decide), H.bx], by rw [g _ (by decide), H.r15],
        ⟨by rw [g _ (by decide), H.bx], by rw [w]; exact H.w, H.fit, by rw [g _ (by decide), H.rsp]; exact H.stk,
          rc_keep H.env.rc fun q h₁ h₂ => keepS f fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact dS S (.inl (by rw [laneB0]; omega_using [h₂])) (by omega_using [h₂]) (by rw [laneB0]; omega_using [hn32])⟩,
        by rw [g _ (by decide), H.rsp]⟩
  have sC : ∀ y, B y → WP isa (Impl.SlhDsa.X86_64.thashCall ⟨p.n, p.len⟩ name T.code Layout.oB Layout.strideB
      ((⟨p.n, p.len⟩ : Layout).n + 32 + p.k * (⟨p.n, p.len⟩ : Layout).n)) y
      fun z => z.gpr .rbx = S ∧ z.gpr .r15 = at' S Layout.oMsg := fun y ⟨hb, h15, O, _⟩ =>
    WP.mono (t4g_ok T name hn hst hs63 (o := Layout.oB) (st := Layout.strideB) (len := p.n + 32 + p.k * p.n)
      (.inr ⟨rfl, rfl⟩) (by omega_using []) (by omega_using [hn8, hkn8])
      (by simp only [Layout.strideB]; omega_using [hkn, hn32]) O.bx O.wr O.fit O.stk O.rc) fun z C =>
      ⟨by rw [C.cs _ (by simp [calleeSaved]), hb], by rw [C.cs _ (by simp [calleeSaved]), h15]⟩
  unfold pkFors
  refine Levels.relSeq (B₁ := B) (B₂ := B) (ForsCT.ct_pkf hp6 fun x y ⟨hx, hy⟩ r hr => ?_) (fun x h => sF x h)
    (fun x h => sF x h) ?_
  · simp only [List.mem_singleton] at hr; subst hr; rw [hx.bx, hy.bx]
  refine Levels.relSeq (t4g_ct hp6 T name hst hs63 (.inr ⟨rfl, rfl⟩) (by dsimp only; omega_using [])
    (by dsimp only; omega_using [hn8, hkn8]) (by dsimp only; simp only [Layout.strideB]; omega_using [hkn, hn32])
    (fun y h => ⟨h.2.2.1, h.2.2.2⟩) (fun y h => ⟨h.2.2.1, h.2.2.2⟩)) sC sC ?_
  exact ForsCT.ct_pkc hp6 fun x y ⟨hx, hy⟩ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hx.1, hy.1]
    · rw [hx.2, hy.2]

/-! ## `forsSign` is constant time -/

theorem fors_ct (hp : FSet p) (T : Thash4Impl p.n) (name ln : String) {stack : Nat} (hst : T.stack + 24 ≤ stack)
    (hs63 : stack < 2 ^ 63) :
    ConstantTime isa (forsContract p stack).pre (forsContract p stack).pub
      (Impl.SlhDsa.X86_64.Fors.forsSign ⟨p.n, p.len⟩ p.a p.k name ln T.code) := by
  obtain ⟨hf, hn, -, -, hk1, hk35, -, -⟩ := hp.facts
  have hp6 : P6 p := hp.2
  intro s₁ s₂ tr₁ tr₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  obtain ⟨hp1, hp2, hp3⟩ := hpub
  obtain ⟨R₁, ⟨pk₁, a₁, hE₁⟩, hkp₁⟩ := h₁
  obtain ⟨R₂, ⟨pk₂, a₂, hE₂⟩, hkp₂⟩ := h₂
  generalize hS : s₁.gpr .rdi = S at R₁ hE₁
  generalize hG : s₁.gpr .rsi = SG at R₁
  have hS₂ : s₂.gpr .rdi = S := by rw [← hp1, hS]
  have hG₂ : s₂.gpr .rsi = SG := by rw [← hp2, hG]
  rw [hS₂] at R₂ hE₂
  rw [hG₂] at R₂
  have hix : ∀ (m : Mem), ∀ i < p.k, ixv m S p.a i < 2 ^ p.a := fun m i _ => Nat.mod_lt _ (Nat.two_pow_pos _)
  have pkh : ∀ {σ : State} {pk a : List Byte} {t t₁ : State}, Front p stack σ S SG t →
      TL p stack S SG pk a (bytesAt σ.mem (at' S Layout.oSkSeed) p.n) (ixv σ.mem S p.a) t p.k t₁ →
      PkH p stack S (σ.gpr .rsp) pk a t₁ := fun F H =>
    ⟨by rw [H.cs _ (by simp [calleeSaved]) (by decide), F.M.bx],
      by rw [H.cs _ (by simp [calleeSaved]) (by decide)]; exact F.M.kp,
      by rw [H.cs _ (by simp [calleeSaved]) (by decide), F.r15], by rw [H.wr]; exact F.M.w, F.M.fit,
      by rw [H.cs _ (by simp [calleeSaved]) (by decide), F.sp], by rw [← F.sp]; exact F.M.stk, H.env⟩
  have wpk : ∀ {σ : State} {pk a : List Byte} (t₁ : State), (∃ t, Front p stack σ S SG t ∧
      TL p stack S SG pk a (bytesAt σ.mem (at' S Layout.oSkSeed) p.n) (ixv σ.mem S p.a) t p.k t₁) →
      WP isa (pkFors ⟨p.n, p.len⟩ p.k name T.code) t₁ fun t₂ => t₂.gpr .rbx = S := fun t₁ ⟨t, F, H⟩ => by
    have K := pkh F H
    exact WP.mono (pk_ok T name hn hf (by omega_using [hst]) hs63 K.bx K.kp K.r15 K.w K.fit (by rw [K.rsp]; exact K.stk)
      K.env hk35 (bytesAt_flat t₁.mem S (Layout.laneB 0 + p.n + 32) p.n p.k)) fun t₂ ⟨X, _⟩ => by
        rw [X.cs _ (by simp [calleeSaved]), K.bx]
  have hct : RelCT isa (fun a b => a = s₁ ∧ b = s₂)
      (Impl.SlhDsa.X86_64.Fors.forsSign ⟨p.n, p.len⟩ p.a p.k name ln T.code) fun _ _ => True := by
    unfold Impl.SlhDsa.X86_64.Fors.forsSign
    refine Levels.relSeq
      (B₁ := fun t => Front p stack s₁ S SG t ∧
        TL p stack S SG pk₁ a₁ (bytesAt s₁.mem (at' S Layout.oSkSeed) p.n) (ixv s₁.mem S p.a) t 0 t)
      (B₂ := fun t => Front p stack s₂ S SG t ∧
        TL p stack S SG pk₂ a₂ (bytesAt s₂.mem (at' S Layout.oSkSeed) p.n) (ixv s₂.mem S p.a) t 0 t)
      (ForsCT.ct_fpro hp6 fun x y ⟨hx, hy⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr hx hy; rw [hp1])
      (fun x hx => by subst hx; exact front_ok hp hS hG R₁ hE₁ hkp₁)
      (fun y hy => by subst hy; exact front_ok hp hS₂ hG₂ R₂ hE₂ hkp₂) ?_
    refine Levels.relSeq
      (B₁ := fun t₁ => ∃ t, Front p stack s₁ S SG t ∧
        TL p stack S SG pk₁ a₁ (bytesAt s₁.mem (at' S Layout.oSkSeed) p.n) (ixv s₁.mem S p.a) t p.k t₁)
      (B₂ := fun t₁ => ∃ t, Front p stack s₂ S SG t ∧
        TL p stack S SG pk₂ a₂ (bytesAt s₂.mem (at' S Layout.oSkSeed) p.n) (ixv s₂.mem S p.a) t p.k t₁) ?_
      (fun x ⟨F, I⟩ => WP.mono (trees_ok T name ln hst hs63 F.M (hix _) hk1 (Nat.zero_add _) I) fun y h => ⟨x, F, h⟩)
      (fun x ⟨F, I⟩ => WP.mono (trees_ok T name ln hst hs63 F.M (hix _) hk1 (Nat.zero_add _) I) fun y h => ⟨x, F, h⟩) ?_
    · intro x y v₁ v₂ x' y' ⟨⟨F₁, I₁⟩, ⟨F₂, I₂⟩⟩ e₁ e₂
      exact ⟨(trees_ct hp T name ln hst hs63 F₁.M F₂.M (hix _) (hix _) (by rw [F₁.sp, F₂.sp, hp3]) p.k _ _ _ _ _ _
        ⟨⟨0, Nat.zero_add _, hk1, I₁⟩, ⟨0, Nat.zero_add _, hk1, I₂⟩⟩ e₁ e₂).1, trivial⟩
    refine Levels.relSeq (B₁ := fun t => t.gpr .rbx = S) (B₂ := fun t => t.gpr .rbx = S)
      (RelCT.mono (pk_ct hp T name (by omega_using [hst]) hs63 (sp := s₁.gpr .rsp)) (fun a b ⟨⟨t, F, H⟩, ⟨t', F', H'⟩⟩ =>
        ⟨pkh F H, by have := pkh F' H'; rw [← hp3] at this; exact this⟩) fun _ _ h => h)
      (fun x h => wpk x h) (fun x h => wpk x h)
      (ForsCT.ct_rest fun x y ⟨hx, hy⟩ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [hx, hy])
  exact (hct s₁ s₂ tr₁ tr₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `Verified` -/

/-- `forsSign` for the SHAKE parameter sets, with any `thash4`. -/
theorem fors_verified (hp : FSet p) (T : Thash4Impl p.n) (name ln : String) :
    Verified X86_64.target (Impl.SlhDsa.X86_64.Fors.forsSign ⟨p.n, p.len⟩ p.a p.k name ln T.code)
      (forsContract p (T.stack + 24)) := by
  have hs : T.stack + 24 < 2 ^ 63 := by have := T.stack_le; omega_using [this]
  exact ⟨fors_correct hp T name ln (Nat.le_refl _) hs, fors_ct hp T name ln (Nat.le_refl _) hs,
    ⟨forsSat p, forsSat_pre hp hs⟩⟩

end VG.Proof.SlhDsa.X86_64.Fors

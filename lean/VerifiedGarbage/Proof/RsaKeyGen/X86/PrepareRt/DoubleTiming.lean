module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareRt.Double
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareRt.SeedTiming
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareRt.Doubles
import VerifiedGarbage.Proof.RsaKeyGen.X86.TimingSeg
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.Blocks
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops2
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # A doubling reads the same addresses in every run

Each loop and store of a doubling is checked with the registers it addresses
through public; every run holds the same pointers and counts at its start,
which the doubling's frame (`Body`) gives. -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PrepareRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.PrepareRt
open VG.Proof.RsaKeyGen.X86 (seg rawBlock ptr_value)
open VG.Proof.RsaKeyGen.X86.Sieve (StackContext)

/-- At a doubling's start, `k + 1` doublings left. -/
structure In (g : Geometry) (q : BitVec 32) (k : Nat) (s : State) : Prop where
  context : Context g s
  stack : StackContext q s
  saved : s.mem.readW (off (q.setWidth 64) 0) 32 = s.gpr .edi
  count : s.gpr .esi = BitVec.ofNat 32 (k + 1)
  bound : k + 1 < 2 ^ 32

/-- Within a doubling started at `a`. -/
def Body (g : Geometry) (q : BitVec 32) (k : Nat) (a s : State) : Prop :=
  In g q k a ∧ Outs g.W (doubleRanges g) a.mem s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] a s

section
variable {g : Geometry} {q : BitVec 32} {k : Nat} {a s : State}

theorem doubleRanges_above (v : g.Valid) : ∀ r ∈ doubleRanges g, 256 ≤ r.1 := fun r mem => by
  have := v.arrayHeader 2
  have := v.arrayHeader 6
  simp only [doubleRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl <;> omega

theorem Body.ws (B : Body g q k a s) : Ws s g.W g.L := B.1.context.ws.of_keeps B.2.2

theorem Body.stack (B : Body g q k a s) : StackContext q s := B.1.stack.keep B.2.2 (by decide)

theorem Body.context (v : g.Valid) (B : Body g q k a s) (edi : s.gpr .edi = a.gpr .edi) : Context g s :=
  Context.restore B.1.context B.2.2.2.2 edi B.2.1 (doubleRanges_above v)

theorem Body.saved (v : g.Valid) (apart : (⟨g.W, g.L⟩ : Region).Disjoint ⟨q.setWidth 64, 20⟩)
    (B : Body g q k a s) : s.mem.readW (off (q.setWidth 64) 0) 32 = a.gpr .edi := by
  rw [← B.1.saved]
  exact Mem.readW_congr fun j hj => B.2.1 _ (far_of_apart v apart j hj)

theorem Body.step {t : State} (B : Body g q k a s) {rs : List Reg} (K : Keeps rs s t)
    (sub : ∀ r ∈ rs, r ∈ [.eax, .ebx, .ecx, .edx, .ebp, .edi] := by decide) {o n : Nat}
    (O : Outside g.W o n s.mem t.mem) (mem : (o, n) ∈ doubleRanges g) : Body g q k a t :=
  ⟨B.1, B.2.1.trans (Outs.of_outside O mem), B.2.2.trans (K.mono sub)⟩

theorem Body.same {t : State} (B : Body g q k a s) {rs : List Reg} (K : Keeps rs s t)
    (sub : ∀ r ∈ rs, r ∈ [.eax, .ebx, .ecx, .edx, .ebp, .edi] := by decide) (M : t.mem = s.mem) :
    Body g q k a t :=
  ⟨B.1, by rw [M]; exact B.2.1, B.2.2.trans (K.mono sub)⟩

end

/-- The carry stored above the sum. -/
theorem carry_frame {s : State} {W : Addr} {L x : Nat} (hw : Ws s W L) (P : PtrAt s W .ebp x) (fit : x + 4 ≤ L) :
    WP isa (.block carry) s fun t => Outside W x 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold carry
  refine wp_movS rfl fun e1 E1 _ => wp_subS rfl fun e2 E2 _ => ?_
  have K2 : Keeps [.eax] s e2 := E1.keeps.trans E2.keeps
  have hw2 := hw.of_keeps K2
  have P2 : PtrAt e2 W .ebp x := by rw [PtrAt, K2.1 .ebp (by decide)]; exact P
  refine wp_storeS (ea_ptr hw2 P2 (d := 0) (by omega)) (ws_write hw2 (y := x + 0) (n := 4) (by omega))
    fun e E => WP.block_nil ⟨?_, K2.widen (E.keeps [])⟩
  rw [E.mem, E2.mem, E1.mem, Nat.add_zero]
  exact writeW32_outside _ _ _ (by have := hw.nowrap; omega)

/-- The selection's mask, whatever the carry. -/
theorem below_frame {h : State} {W : Addr} {L x : Nat} (hw : Ws h W L) (P : PtrAt h W .ebp x) (fit : x + 4 ≤ L)
    {q : BitVec 32} (St : StackContext q h) {c1 : Bool} (mask : h.gpr .ecx = cmask c1) :
    WP isa (.block VG.Impl.RsaKeyGen.X86.PrepareRt.below) h fun i =>
      (∃ b, i.gpr .ecx = cmask b) ∧ i.gpr .edi = h.mem.readW (off (q.setWidth 64) 0) 32 ∧ i.mem = h.mem ∧
      Keeps [.eax, .ecx, .edi] h i := by
  unfold VG.Impl.RsaKeyGen.X86.PrepareRt.below
  refine wp_movS (readSrc_ptr hw P (d := 0) (by omega)) fun i1 I1 _ => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_carry (c := c1) (by rw [I1.other .ecx (by decide)]; exact mask)
    fun i2 I2 cf2 => ?_
  refine wp_sbbS rfl cf2 fun i3 I3 cf3 => wp_sbb_self cf3 fun i4 I4 => wp_movS rfl fun i5 I5 _ => ?_
  have K5 : Keeps [.eax, .ecx] h i5 :=
    ((((I1.keeps.mono (by decide)).widen I2.keeps).widen I3.keeps).widen I4.keeps).widen I5.keeps
  have M5 : i5.mem = h.mem := by rw [I5.mem, I4.mem, I3.mem, I2.mem, I1.mem]
  refine wp_movS ((St.keep K5 (by decide)).read 0 (by decide)) fun i I _ => WP.block_nil ?_
  refine ⟨⟨decide ((i2.gpr .eax).toNat < BitVec.toNat (0 : BitVec 32) + c1.toNat), ?_⟩, by rw [I.gpr, M5],
    by rw [I.mem, M5], (K5.mono (by decide)).widen I.keeps⟩
  rw [I.other .ecx (by decide), I5.gpr, I4.gpr]

section
variable {g : Geometry} {q : BitVec 32} {k : Nat}

/-- Within a doubling, with what its next segment needs. -/
def At (g : Geometry) (q : BitVec 32) (k : Nat) (E : State → State → Prop) (s : State) : Prop :=
  ∃ a, Body g q k a s ∧ E a s

theorem doubleLoop_raw : RelCT isa (VG.X86.Taint.Agree (τr [.ebx, .ebp, .edx])) doubleLoop (fun _ _ => True) :=
  (erased_relCT (σ := τr []) doubleLoop doubleLoop (VG.Taint.hintOf taint (τr [.ebx, .ebp, .edx]) (Code.erase doubleLoop))
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem reduceLoop_raw : RelCT isa (VG.X86.Taint.Agree (τr [.ebp, .ebx, .edi, .edx])) reduceLoop (fun _ _ => True) :=
  (erased_relCT (σ := τr []) reduceLoop reduceLoop
    (VG.Taint.hintOf taint (τr [.ebp, .ebx, .edi, .edx]) (Code.erase reduceLoop))
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem selectLoop_raw : RelCT isa (VG.X86.Taint.Agree (τr [.ebp, .ebx, .edi])) selectLoop (fun _ _ => True) :=
  (erased_relCT (σ := τr []) selectLoop selectLoop
    (VG.Taint.hintOf taint (τr [.ebp, .ebx, .edi]) (Code.erase selectLoop))
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

/-- A doubling's end: one fewer left, and `ZF` set at the last. -/
def Done (g : Geometry) (q : BitVec 32) (k : Nat) (t : State) : Prop :=
  t.zf = some (decide (k = 0)) ∧ (k ≠ 0 → In g q (k - 1) t)

/-- At a block that reads the header: `edi` back at the workspace. -/
abbrev Base (g : Geometry) (q : BitVec 32) (k : Nat) : State → Prop :=
  At g q k fun a s => s.gpr .edi = a.gpr .edi

theorem sum_trace (v : g.Valid) :
    RelCT isa (fun s t => Base g q k s ∧ Base g q k t) sum (fun u z => Base g q k u ∧ Base g q k z) := by
  obtain ⟨fit6, -, many, -⟩ := WitnessRt.fits v
  have a26 : g.array 2 + 4 * g.words + 4 ≤ g.array 6 := by
    unfold Geometry.array Geometry.words Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes; omega
  unfold sum
  let Loop : State → Prop := At g q k fun a s => PtrAt s g.W .ebx (g.array 6) ∧ PtrAt s g.W .ebp (g.array 2) ∧
    (s.gpr .edx).toNat = 4 * g.words ∧ s.gpr .ecx = cmask false ∧ s.gpr .edi = a.gpr .edi
  let Carry : State → Prop := At g q k fun a s => PtrAt s g.W .ebp (g.array 2 + 4 * g.words) ∧
    s.gpr .edi = a.gpr .edi
  refine RelCT.seq (R := fun u z => Loop u ∧ Loop z)
    (baseSeg (g := g) (fun _ ⟨_, B, edi⟩ => B.context v edi) (rawBlock (by decide +kernel)) fun s ⟨a, B, edi⟩ =>
      WP.mono (doubleArgs_ok v (B.context v edi)) fun _ ⟨Px, Pa, edx, ecx, M, K⟩ =>
        ⟨a, B.same K (by decide) M, Px, Pa, edx, ecx, (K.1 .edi (by decide)).trans edi⟩)
    (RelCT.seq (R := fun u z => Carry u ∧ Carry z) ?_ ?_)
  · refine seg [.ebx, .ebp, .edx] (fun r => if r = .ebx then BitVec.ofNat 32 (g.W.toNat + g.array 6)
      else if r = .ebp then BitVec.ofNat 32 (g.W.toNat + g.array 2) else BitVec.ofNat 32 (4 * g.words))
      (fun s ⟨_, _, Px, Pa, edx, _⟩ r mem => ?_) doubleLoop_raw fun s ⟨a, B, Px, Pa, edx, ecx, edi⟩ =>
        WP.mono (VG.Proof.Bignum.X86.PublicRt.doubleLoop_ok B.ws (x := g.array 6) (a := g.array 2) (N := g.words)
          (by omega) fit6 (by omega) (Or.inl (by omega)) Px Pa edx ecx) fun _ ⟨O, P, _, K⟩ =>
          ⟨a, B.step K (by decide) (O.mono (o' := g.array 2) (n' := 4 * g.words + 4) (by omega) (by omega))
            (by simp [doubleRanges]), P, (K.1 .edi (by decide)).trans edi⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl
    · exact ptr_value Px
    · exact ptr_value Pa
    · exact nat_at edx
  · exact ptrSeg .ebp (g.array 2 + 4 * g.words) (fun _ ⟨_, _, P, _⟩ => P) (rawBlock (by decide +kernel))
      fun s ⟨a, B, P, edi⟩ => WP.mono (carry_frame B.ws P (by omega)) fun _ ⟨O, K⟩ =>
        ⟨a, B.step K (by decide) (O.mono (o' := g.array 2) (n' := 4 * g.words + 4) (by omega) (by omega))
          (by simp [doubleRanges]), (K.1 .edi (by decide)).trans edi⟩


/-- After the subtraction: `ebp` above the sum and a mask in `ecx`. -/
abbrev Masked (g : Geometry) (q : BitVec 32) (k : Nat) : State → Prop :=
  At g q k fun _ s => PtrAt s g.W .ebp (g.array 2 + 4 * g.words) ∧ ∃ b, s.gpr .ecx = cmask b

theorem reduce_trace (v : g.Valid) :
    RelCT isa (fun s t => Base g q k s ∧ Base g q k t) reduce (fun u z => Masked g q k u ∧ Masked g q k z) := by
  obtain ⟨fit6, -, many, -⟩ := WitnessRt.fits v
  have a26 : g.array 2 + 4 * g.words + 4 ≤ g.array 6 := by
    unfold Geometry.array Geometry.words Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes; omega
  have a02 : g.array 0 + 4 * g.words ≤ g.array 2 := g.arrayBefore (by decide)
  unfold reduce
  let Loop : State → Prop := At g q k fun _ s => PtrAt s g.W .ebp (g.array 2) ∧ PtrAt s g.W .ebx (g.array 0) ∧
    PtrAt s g.W .edi (g.array 6) ∧ (s.gpr .edx).toNat = 4 * g.words ∧ s.gpr .ecx = cmask false
  refine RelCT.seq (R := fun u z => Loop u ∧ Loop z)
    (baseSeg (g := g) (fun _ ⟨_, B, edi⟩ => B.context v edi) (rawBlock (by decide +kernel)) fun s ⟨a, B, edi⟩ =>
      WP.mono (reduceArgs_ok v (B.context v edi)) fun _ ⟨Pa, Pm, Pd, edx, ecx, M, K⟩ =>
        ⟨a, B.same K (by decide) M, Pa, Pm, Pd, edx, ecx⟩) ?_
  refine seg [.ebp, .ebx, .edi, .edx] (fun r => if r = .ebp then BitVec.ofNat 32 (g.W.toNat + g.array 2)
    else if r = .ebx then BitVec.ofNat 32 (g.W.toNat + g.array 0)
    else if r = .edi then BitVec.ofNat 32 (g.W.toNat + g.array 6) else BitVec.ofNat 32 (4 * g.words))
    (fun s ⟨_, _, Pa, Pm, Pd, edx, _⟩ r mem => ?_) reduceLoop_raw fun s ⟨a, B, Pa, Pm, Pd, edx, ecx⟩ =>
      WP.mono (VG.Proof.Bignum.X86.PublicRt.reduceLoop_ok B.ws (a := g.array 2) (m := g.array 0) (d := g.array 6)
        (N := g.words) (by omega) (by omega) (by omega) fit6 (Or.inr (by omega)) (Or.inr (by omega)) Pa Pm Pd edx ecx)
        fun _ ⟨O, P, ⟨c, mask, _⟩, K⟩ => ⟨a, B.step K (by decide) O (by simp [doubleRanges]), P, c, mask⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl
  · exact ptr_value Pa
  · exact ptr_value Pm
  · exact ptr_value Pd
  · exact nat_at edx

/-- After the mask: `edi` back at the workspace. -/
abbrev Choosing (g : Geometry) (q : BitVec 32) (k : Nat) : State → Prop :=
  At g q k fun a s => s.gpr .edi = a.gpr .edi ∧ ∃ b, s.gpr .ecx = cmask b

theorem below_trace (v : g.Valid) (apart : (⟨g.W, g.L⟩ : Region).Disjoint ⟨q.setWidth 64, 20⟩) :
    RelCT isa (fun s t => Masked g q k s ∧ Masked g q k t) (.block VG.Impl.RsaKeyGen.X86.PrepareRt.below)
      (fun u z => Choosing g q k u ∧ Choosing g q k z) := by
  obtain ⟨fit6, -, -, -⟩ := WitnessRt.fits v
  have a26 : g.array 2 + 4 * g.words + 4 ≤ g.array 6 := by
    unfold Geometry.array Geometry.words Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes; omega
  refine seg [.ebp, .esp] (fun r => if r = .ebp then BitVec.ofNat 32 (g.W.toNat + (g.array 2 + 4 * g.words))
    else q) (fun s ⟨_, B, P, _⟩ r mem => ?_) (rawBlock (by decide +kernel)) fun s ⟨a, B, P, b, mask⟩ =>
      WP.mono (below_frame B.ws P (by omega) B.stack mask) fun _ ⟨chosen, edi, M, K⟩ =>
        ⟨a, B.same K (by decide) M, by rw [edi, B.saved v apart], chosen⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact ptr_value P
  · exact B.stack.sp

/-- The workspace pointer back, and one doubling fewer left. -/
theorem next_done (v : g.Valid) (apart : (⟨g.W, g.L⟩ : Region).Disjoint ⟨q.setWidth 64, 20⟩) {a s : State}
    (B : Body g q k a s) : WP isa (.block next) s (Done g q k) := by
  have I := B.1
  unfold next
  refine wp_movS (B.stack.read 0 (by decide)) fun t1 T1 _ => wp_subZ rfl fun t T zt => WP.block_nil ?_
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi, .esi] a t :=
    (B.2.2.mono (by decide)).trans ((T1.keeps.mono (by decide)).widen T.keeps)
  have edi : t.gpr .edi = a.gpr .edi := by rw [T.other .edi (by decide), T1.gpr, B.saved v apart]
  have Mt : t.mem = s.mem := by rw [T.mem, T1.mem]
  have esiT1 : (t1.gpr .esi).toNat = (k + 1) - 0 := by
    rw [T1.other .esi (by decide), B.2.2.1 .esi (by decide), I.count, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt I.bound, Nat.sub_zero]
  obtain ⟨step, last⟩ := VG.Proof.Bignum.X86.PublicRt.count1_zf esiT1 (by omega)
  refine ⟨by rw [zt, last]; congr 1; exact decide_eq_decide.mpr (by omega), fun positive => ?_⟩
  have O : Outs g.W (doubleRanges g) a.mem t.mem := by rw [Mt]; exact B.2.1
  refine ⟨Context.restore I.context Kall.2.2 edi O (doubleRanges_above v), I.stack.keep Kall (by decide),
    by rw [Mt, B.saved v apart, edi], ?_, by have := I.bound; omega⟩
  apply BitVec.eq_of_toNat_eq
  rw [T.gpr, step, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := I.bound; omega)]
  omega

theorem select_trace (v : g.Valid) (apart : (⟨g.W, g.L⟩ : Region).Disjoint ⟨q.setWidth 64, 20⟩) :
    RelCT isa (fun s t => Choosing g q k s ∧ Choosing g q k t) select (fun u z => Done g q k u ∧ Done g q k z) := by
  obtain ⟨fit6, -, many, -⟩ := WitnessRt.fits v
  have a26 : g.array 2 + 4 * g.words + 4 ≤ g.array 6 := by
    unfold Geometry.array Geometry.words Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes; omega
  unfold select
  let Loop : State → Prop := At g q k fun _ s => PtrAt s g.W .ebp (g.array 2) ∧ PtrAt s g.W .ebx (g.array 6) ∧
    (s.gpr .edi).toNat = 4 * g.words ∧ ∃ b, s.gpr .ecx = cmask b
  let Next : State → Prop := At g q k fun _ _ => True
  refine RelCT.seq (R := fun u z => Loop u ∧ Loop z)
    (baseSeg (g := g) (fun _ ⟨_, B, edi, _⟩ => B.context v edi) (rawBlock (by decide +kernel))
      fun s ⟨a, B, edi, b, mask⟩ => WP.mono (selectArgs_ok v (B.context v edi)) fun _ ⟨Pa, Pd, count, M, K⟩ =>
        ⟨a, B.same K (by decide) M, Pa, Pd, count, b, by rw [K.1 .ecx (by decide)]; exact mask⟩)
    (RelCT.seq (R := fun u z => Next u ∧ Next z) ?_ ?_)
  · refine seg [.ebp, .ebx, .edi] (fun r => if r = .ebp then BitVec.ofNat 32 (g.W.toNat + g.array 2)
      else if r = .ebx then BitVec.ofNat 32 (g.W.toNat + g.array 6) else BitVec.ofNat 32 (4 * g.words))
      (fun s ⟨_, _, Pa, Pd, count, _⟩ r mem => ?_) selectLoop_raw fun s ⟨a, B, Pa, Pd, count, b, mask⟩ =>
        WP.mono (VG.Proof.Bignum.X86.PublicRt.selectLoop_ok B.ws (x := g.array 2) (d := g.array 6) (N := g.words) b
          (by omega) (by omega) fit6 (Or.inr (by omega)) Pa Pd count mask) fun _ ⟨O, _, _, K⟩ =>
          ⟨a, B.step K (by decide) O (by simp [doubleRanges]), trivial⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl
    · exact ptr_value Pa
    · exact ptr_value Pd
    · exact nat_at count
  · exact seg [.esp] (fun _ => q) (fun s ⟨_, B, _⟩ r mem => by
      obtain rfl := List.mem_singleton.mp mem; exact B.stack.sp) (rawBlock (by decide +kernel))
      fun s ⟨a, B, _⟩ => next_done v apart B

theorem double_trace (v : g.Valid) (apart : (⟨g.W, g.L⟩ : Region).Disjoint ⟨q.setWidth 64, 20⟩) :
    RelCT isa (fun s t => In g q k s ∧ In g q k t) double (fun u z => Done g q k u ∧ Done g q k z) := by
  unfold double
  exact (RelCT.seq (sum_trace v) (RelCT.seq (reduce_trace v) (RelCT.seq (below_trace v apart)
    (select_trace v apart)))).mono
    (fun s t ⟨S, T⟩ => ⟨⟨s, ⟨S, Outs.refl _ _ _, Keeps.refl _ _⟩, rfl⟩, ⟨t, ⟨T, Outs.refl _ _ _, Keeps.refl _ _⟩, rfl⟩⟩)
    (fun _ _ H => H)


end

theorem doublings_trace {g : Geometry} {q : BitVec 32} (v : g.Valid)
    (apart : (⟨g.W, g.L⟩ : Region).Disjoint ⟨q.setWidth 64, 20⟩) (k : Nat) :
    RelCT isa (fun s t => In g q k s ∧ In g q k t) (.loop double .ne) (fun _ _ => True) := by
  let Inv : Nat → State → State → Prop := fun n s t => ∃ j, n = j + 1 ∧ In g q j s ∧ In g q j t
  refine (RelCT.loop (M := isa) (Q := fun _ _ => True) Inv ?_ (k + 1)).mono (fun s t H => ⟨k, rfl, H⟩)
    (fun _ _ _ => trivial)
  rintro n s t tr ur u z ⟨j, rfl, H⟩ E G
  obtain ⟨trace, ⟨zu, U⟩, ⟨zz, Z⟩⟩ := double_trace (k := j) v apart _ _ _ _ _ _ H E G
  refine ⟨trace, by simp only [eval, zu, zz], fun _ => trivial, fun again => ?_⟩
  have positive : j ≠ 0 := by
    intro zero
    simp only [eval, zu, zero, decide_true, Option.map_some, Bool.not_true] at again
    cases again
  exact ⟨j, by omega, j - 1, by omega, U positive, Z positive⟩

end VG.Proof.RsaKeyGen.X86.PrepareRt

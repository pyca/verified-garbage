module

public import VerifiedGarbage.Proof.Dsa.X86.RedTiming
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Dsa.X86.PowCallFrame
import VerifiedGarbage.Proof.Dsa.X86.RedVerified
import VerifiedGarbage.Proof.Dsa.X86.PowCorrect
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Spec.Dsa

/-! # Calls of the IA-32 DSA reduction

The caller passes the working space, its length, and the bytes' address and
length (`esi`, `ebx`) as cdecl's four stack arguments (`reduceCall`). -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Red
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Arith
open VG.Proof.Dsa.X86 (StreamInput callStack)
open VG.Proof.Dsa.X86.Pow (ws bytes)

abbrev pushes : List Reg := [.ebx, .esi, .eax, .edi]

/-- The callee's argument `i`, `16 - 4 i` bytes below the caller's `esp`. -/
theorem argAddr_entry (s : State) (i : Nat) (hi : i < 4) :
    argAddr (pushed pushes s).callEntry i = (s.gpr .esp - BitVec.ofNat 32 (16 - 4 * i)).setWidth 64 := by
  unfold argAddr
  rw [callEntry_esp']
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, List.length_cons, List.length_nil]
  have := (s.gpr .esp).isLt
  omega

theorem sub_toNat64 (e : BitVec 32) {k : Nat} (h : k ≤ e.toNat) :
    ((e - BitVec.ofNat 32 k).setWidth 64).toNat = e.toNat - k := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := e.isLt
  omega

/-- What the caller provides for a reduction of the `len` bytes at `p`, with
the modulus `m` in slot 0. -/
structure CallIn (n m : Nat) (s : State) (base : Addr) (size : Nat) (p : BitVec 32) (len : Nat) : Prop where
  scr : Scr s base size
  room : Pow.Room (s.gpr .esp) base size
  context : contextBytes n ≤ size
  modulus : wordsVal s.mem base (slot n 0) n = m
  large : 255 < m
  odd : m % 2 = 1
  esi : s.gpr .esi = p
  ebx : s.gpr .ebx = BitVec.ofNat 32 len
  lenFit : len < 2 ^ 32
  input : StreamInput s base (contextBytes n) p len
  stack : Region.Disjoint ⟨p.setWidth 64, len⟩ (callStack (s.gpr .esp))

theorem CallIn.sp {n m : Nat} {s : State} {base : Addr} {size : Nat} {p : BitVec 32} {len : Nat}
    (C : CallIn n m s base size p len) : 108 ≤ (s.gpr .esp).toNat := C.room.1

/-- The memory of the callee's entry is the caller's but for the 20 bytes
below `esp`. -/
theorem entry_frame (s : State) (h : 20 ≤ (s.gpr .esp).toNat) :
    Frame [below (s.gpr .esp) 20] s.mem (pushed pushes s).callEntry.mem :=
  callEntry_frame (rs := pushes) (by simp; omega) (by decide)

/-- Below `esp` within the call's stack, apart from the working space. -/
theorem below_apart {sp : BitVec 32} {base : Addr} {size k : Nat} (room : Pow.Room sp base size)
    (hn : base.toNat + size ≤ 2 ^ 32) (hk : k ≤ 108) {sz : Nat} (hsz : sz ≤ size) {x : Addr}
    (hx : (below sp k).Contains x 1) : ¬ (⟨base, sz⟩ : Region).Contains x 1 := by
  have := Pow.zone_ofs' room hn hk hx
  simp only [Region.Contains, ofs] at this ⊢
  omega

theorem frame_val32 {sp : BitVec 32} {base : Addr} {size : Nat}
    (H : Pow.Room sp base size) (hn : base.toNat + size ≤ 2 ^ 32)
    {m m' : Mem} (F : Frame [below sp 20] m m') {d k : Nat} (hd : d + 4 * k ≤ size) :
    val32 m' base d k = val32 m base d k := by
  refine val32_congr fun j hj => congrArg BitVec.toNat (Mem.readW_congr fun i hi => F _ fun r hr hc => ?_)
  rw [List.mem_singleton.mp hr] at hc
  have := Pow.zone_ofs' H hn (by decide) hc
  rw [ofs_off base (by omega)] at this
  omega

theorem entry_bodyIn {n m : Nat} {s : State} {base : Addr} {size sz : Nat} {p : BitVec 32} {len : Nat}
    (C : CallIn n m s base size p len) (hsz : contextBytes n ≤ sz) (hsz' : sz ≤ size)
    {rd wr : List Region} (hargs : below (s.gpr .esp) 16 ∈ rd ++ wr)
    (hdata : InRegions (rd ++ wr) (p.setWidth 64) len) (hws : (⟨base, sz⟩ : Region) ∈ wr) :
    BodyIn n sz ((pushed pushes s).callEntry.withRegions rd wr) := by
  have hsp := C.sp
  have nw := C.scr.nowrap
  have lf := C.lenFit
  have fit : 4 * pushes.length + 4 ≤ (s.gpr .esp).toNat := by simp; omega
  have a0 : arg ((pushed pushes s).callEntry.withRegions rd wr) 0 = s.gpr .edi :=
    callEntry_arg fit (by decide) (by decide)
  have a2 : arg ((pushed pushes s).callEntry.withRegions rd wr) 2 = p :=
    (callEntry_arg fit (by decide) (by decide)).trans C.esi
  have a3 : arg ((pushed pushes s).callEntry.withRegions rd wr) 3 = BitVec.ofNat 32 len :=
    (callEntry_arg fit (by decide) (by decide)).trans C.ebx
  have hws' : ws ((pushed pushes s).callEntry.withRegions rd wr) = base := by
    simp only [ws, a0]; exact C.scr.edi
  have argIn (i : Nat) (hi : i < 4) :
      InRegions (((pushed pushes s).callEntry.withRegions rd wr).rd ++
        ((pushed pushes s).callEntry.withRegions rd wr).wr)
        (argAddr ((pushed pushes s).callEntry.withRegions rd wr) i) 4 := by
    refine ⟨_, hargs, ?_⟩
    rw [argAddr_withRegions, argAddr_entry s i hi]
    exact below_top (by omega) (by omega) (by omega)
  have argApart (i : Nat) (hi : i < 4) :
      Region.Disjoint ⟨argAddr ((pushed pushes s).callEntry.withRegions rd wr) i, 4⟩ ⟨base, sz⟩ := by
    rw [argAddr_withRegions, argAddr_entry s i hi]
    intro x h₁ h₂
    have top : (below (s.gpr .esp) 16).Contains ((s.gpr .esp - BitVec.ofNat 32 (16 - 4 * i)).setWidth 64) 4 :=
      below_top (by omega) (by omega) (by omega)
    have inner := Region.Contains.byte top (by simp only [Region.Contains] at h₁; exact Nat.lt_of_succ_le h₁)
    exact below_apart C.room nw (by decide : 16 ≤ 108) hsz' inner h₂
  have M : wordsVal ((pushed pushes s).callEntry.withRegions rd wr).mem base (slot n 0) n =
      wordsVal s.mem base (slot n 0) n := by
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    exact frame_val32 C.room nw (entry_frame s (by omega))
      (by have := C.context; simp only [contextBytes, slot, stride] at this ⊢; omega)
  refine ⟨?_, hsz, ?_, ?_⟩
  · rw [hws', a2, a3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt C.lenFit]
    refine ⟨⟨argIn 0 (by decide), by rw [a0]; exact C.scr.edi, hws, by omega, ?_⟩, argIn 2 (by decide),
      argIn 3 (by decide), argApart 2 (by decide), argApart 3 (by decide), a2, a3, C.lenFit,
      ⟨C.input.fit, fun i hi => by
        obtain ⟨r, hr, hc⟩ := hdata
        exact ⟨r, hr, Region.Contains.byte hc (by rw [Mem.sub_ofNat_toNat _ (by omega)]; exact hi)⟩,
        C.input.far, hdata⟩⟩
    show StkOk ((pushed pushes s).callEntry.gpr .esp) base sz
    have R := C.room
    unfold StkOk Pow.Room at *
    rw [callEntry_espNat fit]
    simp only [List.length_cons, List.length_nil]
    omega
  · rw [hws', M, C.modulus]; exact C.large
  · rw [hws', M, C.modulus]; exact C.odd

theorem body_noSp (n : Nat) : NoSp (reduceBody n) := NoSp.of_all rfl

theorem body_stackUse (n : Nat) : stackUse (reduceBody n) = 0 := rfl

theorem body_spSafe (n : Nat) : (reduceBody n).allInstrs (fun i => !isa.writesSp i) = true := rfl

theorem CallIn.eax {n m : Nat} {s t : State} {base : Addr} {size : Nat} {p : BitVec 32} {len : Nat}
    (C : CallIn n m s base size p len) (K : Keeps [.eax] s t) (M : t.mem = s.mem) :
    CallIn n m t base size p len := by
  have esp : t.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  refine ⟨C.scr.of_keeps K (by decide), by rw [esp]; exact C.room, C.context, by rw [M]; exact C.modulus,
    C.large, C.odd, by rw [K.1 _ (by decide)]; exact C.esi, by rw [K.1 _ (by decide)]; exact C.ebx, C.lenFit,
    ⟨C.input.fit, by rw [K.2.1, K.2.2]; exact C.input.read, C.input.far, by rw [K.2.1, K.2.2]; exact C.input.whole⟩,
    by rw [esp]; exact C.stack⟩

theorem call_ok {n m : Nat} {s : State} {base : Addr} {size : Nat} {p : BitVec 32} {len : Nat}
    (C : CallIn n m s base size p len) (hused : VG.Impl.Dsa.Layout.usedBytes ≤ size)
    (hn : 0 < n) (hn48 : n ≤ 48) :
    WP isa (reduceCall n) s fun t =>
      wordsVal t.mem base (slot n 6) n = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (p.setWidth 64) len) % m ∧
      StackOuts base (s.gpr .esp) (VG.Impl.Dsa.X86.Pow.scratch n) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx] s t := by
  have hsp := C.sp
  have nw := C.scr.nowrap
  have cb := C.context
  have cb8 : contextBytes n / 8 * 8 = contextBytes n := by simp only [contextBytes, slot, stride]; omega
  unfold reduceCall
  refine WP.seq (wp_movS rfl fun u U _ => WP.block_nil ?_)
  have Cu := C.eax U.keeps U.mem
  have usp : u.gpr .esp = s.gpr .esp := U.other _ (by decide)
  have hu : 108 ≤ (u.gpr .esp).toNat := by rw [usp]; exact hsp
  have fit : 4 * pushes.length + 4 ≤ (u.gpr .esp).toNat := by rw [usp]; simp; omega
  let rd : List Region := [⟨p.setWidth 64, len⟩, below (u.gpr .esp) 16]
  let wr : List Region := [⟨base, contextBytes n⟩]
  let v := (pushed pushes u).callEntry.withRegions rd wr
  have Bv : BodyIn n (contextBytes n) v :=
    entry_bodyIn Cu (Nat.le_refl _) cb (by simp [rd]) ⟨⟨p.setWidth 64, len⟩, by simp [rd], by simp [Region.Contains]⟩ (by simp [wr])
  have a0 : ws v = base := by
    simp only [ws]
    rw [show arg v 0 = u.gpr .edi from callEntry_arg fit (by decide) (by decide)]
    exact Cu.scr.edi
  have vsp : (v.gpr .esp).toNat = (u.gpr .esp).toNat - 20 := callEntry_espNat fit
  let K : Contract isa :=
    { pre := fun w => BodyIn n (contextBytes n) w ∧ ws w = base ∧
        Region.Disjoint ⟨(w.gpr .esp).setWidth 64, 4⟩ ⟨base, contextBytes n⟩
      post := fun w w' => wordsVal w'.mem base (slot n 6) n =
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt w.mem ((arg w 2).setWidth 64) (arg w 3).toNat) %
            wordsVal w.mem base (slot n 0) n ∧
        Outs base (VG.Impl.Dsa.X86.Pow.scratch n) w.mem w'.mem
      pub := fun _ _ => True }
  have ret : Region.Disjoint ⟨(v.gpr .esp).setWidth 64, 4⟩ ⟨base, contextBytes n⟩ := by
    intro x h₁ h₂
    have e : (v.gpr .esp) = u.gpr .esp - BitVec.ofNat 32 20 := by
      apply BitVec.eq_of_toNat_eq; rw [vsp, BitVec.toNat_sub, BitVec.toNat_ofNat]; have := (u.gpr .esp).isLt; omega
    rw [e] at h₁
    have top : (below (u.gpr .esp) 20).Contains ((u.gpr .esp - BitVec.ofNat 32 20).setWidth 64) 4 :=
      below_top (by omega) (by omega) (by omega)
    exact below_apart Cu.room nw (by decide : 20 ≤ 108) cb
      (Region.Contains.byte top (by simp only [Region.Contains] at h₁; exact Nat.lt_of_succ_le h₁)) h₂
  refine WP.callWith (k := K) (fun w ⟨B, W, R⟩ => ?_) (body_noSp n) (by decide) (by decide)
    (by rw [body_stackUse]; simp; omega) (rd := rd) (wr := wr) ⟨⟨Bv, a0, ret⟩, ?_, ?_⟩ ?_
  · rw [← W] at R
    obtain ⟨tr, t, E, A, V, O⟩ := run hn hn48 B R
    rw [W] at V O
    exact ⟨tr, t, E, A, V, O⟩
  · refine Covers.append_left (Covers.cons ?_ (Covers.cons ?_ Covers.nil)) (Covers.cons ?_ Covers.nil)
    · exact (Covers.one Cu.input.whole).trans (Covers.append (Covers.refl _)
        (Covers.of_mem fun r hr => List.mem_cons_of_mem _ hr))
    · exact Covers.of_mem fun r hr => by
        rw [List.mem_singleton.mp hr]; exact List.mem_append_right _ (List.mem_cons_self ..)
    · exact (Covers.one (rs := u.wr) ⟨⟨base, size⟩, Cu.scr.wr, by simp [Region.Contains]; omega⟩).trans
        (Covers.of_mem fun r hr => List.mem_append_right _ (List.mem_cons_of_mem _ hr))
  · refine (Covers.one (rs := u.wr) ⟨⟨base, size⟩, Cu.scr.wr, by simp [Region.Contains]; omega⟩).trans
      (Covers.of_mem fun r hr => List.mem_cons_of_mem _ hr)
  · intro w rdw wrw cs F ⟨w₂, mem, V, O⟩
    rw [body_stackUse] at F
    have Fe : Frame [below (u.gpr .esp) 20] u.mem v.mem := entry_frame u (by omega)
    have a2 : arg v 2 = p := (callEntry_arg fit (by decide) (by decide)).trans Cu.esi
    have a3 : (arg v 3).toNat = len := by
      rw [show arg v 3 = u.gpr .ebx from callEntry_arg fit (by decide) (by decide), Cu.ebx, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt Cu.lenFit]
    have Mv : wordsVal v.mem base (slot n 0) n = m := by
      rw [wordsVal_eq_val32, frame_val32 Cu.room nw Fe
        (by simp only [contextBytes, slot, stride] at cb ⊢; omega), ← wordsVal_eq_val32, Cu.modulus]
    have inStack {x : Addr} (hx : (below (u.gpr .esp) 20).Contains x 1) : (callStack (s.gpr .esp)).Contains x 1 := by
      rw [← usp]; exact below_sub (by decide) hu _ hx
    have Bv : Spec.Rsa.bytesAt v.mem (p.setWidth 64) len = Spec.Rsa.bytesAt s.mem (p.setWidth 64) len := by
      unfold Spec.Rsa.bytesAt
      apply List.map_congr_left
      intro i hi
      have hi' := List.mem_range.mp hi
      rw [← U.mem]
      refine Fe _ fun r hr hc => ?_
      rw [List.mem_singleton.mp hr] at hc
      exact C.stack _ (Offset.contains_base _ (by omega) (by have := C.lenFit; omega)) (inStack hc)
    refine ⟨?_, ?_, ?_⟩
    · rw [← mem, V, a2, a3, Bv, Mv]
    · intro x hx hs
      rw [← U.mem]
      by_cases hin : (⟨base, contextBytes n⟩ : Region).Contains x 1
      · rw [← mem, O x hx]
        refine Fe x fun r hr hc => ?_
        rw [List.mem_singleton.mp hr] at hc
        exact below_apart Cu.room nw (by decide : 20 ≤ 108) cb hc hin
      · by_cases hb : (below (u.gpr .esp) 20).Contains x 1
        · exfalso
          have hz := Pow.zone_ofs' Cu.room nw (by decide : 20 ≤ 108) hb
          rcases hs with lo | hs
          · omega
          · exact hs (inStack hb)
        · refine F x fun r hr => ?_
          simp only [wr, List.mem_append, List.mem_singleton, List.length_cons, List.length_nil] at hr
          rcases hr with rfl | rfl
          · exact hin
          · exact hb
    · refine ⟨fun r hr => ?_, rdw.trans U.rd, wrw.trans U.wr⟩
      have cr : r ∈ calleeSaved := by revert hr; cases r <;> decide
      rw [cs r cr, U.other r (by revert hr; cases r <;> decide)]

theorem body_readArg {n : Nat} {s t : State} {tr : List Leak}
    (E : Exec isa (reduceBody n) s tr t) :
    readSrc s (.mem (at_ .esp 4)) = some (arg s 0) := by
  change s.load32 (argAddr s 0) = some (arg s 0)
  unfold State.load32
  split
  · rfl
  · rename_i h
    cases E with
    | seq E _ =>
      cases E with
      | seq E _ =>
        cases E with
        | block H =>
          simp only [VG.Impl.Dsa.X86.Pow.save, VG.Impl.Dsa.X86.Pow.slots, List.map_cons, List.map_nil,
            List.cons_append, List.nil_append, execBlock, isa, exec, readSrc, State.load32] at H
          simp only [show s.ea (at_ .esp 4) = argAddr s 0 from rfl, h, ↓reduceIte, Option.map_none] at H
          cases H

/-- Two runs about to call the reduction with the same public arguments. -/
def CallPair (n : Nat) (s t : State) : Prop :=
  s.gpr .esp = t.gpr .esp ∧ (∀ r ∈ pushes, s.gpr r = t.gpr r) ∧
    ∃ base size m₁ m₂ p len, CallIn n m₁ s base size p len ∧ CallIn n m₂ t base size p len

theorem entry_self {n m : Nat} {s : State} {base : Addr} {size : Nat} {p : BitVec 32} {len : Nat}
    (C : CallIn n m s base size p len) : BodyIn n size (pushed pushes s).callEntry := by
  have B := entry_bodyIn C C.context (Nat.le_refl _) (rd := (pushed pushes s).callEntry.rd)
    (wr := (pushed pushes s).callEntry.wr)
    (by simp only [State.callEntry_rd, State.callEntry_wr, pushed_rd, pushed_wr]; simp)
    (by
      obtain ⟨r, hr, hc⟩ := C.input.whole
      refine ⟨r, ?_, hc⟩
      simp only [State.callEntry_rd, State.callEntry_wr, pushed_rd, pushed_wr, List.mem_append,
        List.mem_cons] at hr ⊢
      rcases hr with h | h
      · exact .inl h
      · exact .inr (.inr h))
    (by simp only [State.callEntry_wr, pushed_wr]; exact List.mem_cons_of_mem _ C.scr.wr)
  exact B

theorem framed_relCT (n : Nat) (hn : 0 < n) :
    RelCT isa (CallPair n) (.frame (.push pushes) (.call (reduceName n) (reduceBody n)) (.pop .eax 4))
      (fun _ _ => True) := by
  refine RelCT.frame (R := fun _ _ => True) (fun _ _ H => H.1) ?_
  rintro _ _ tr ur sf tf ⟨s, t, ⟨SP, RG, base, size, m₁, m₂, p, len, C₁, C₂⟩, rfl, rfl⟩ E F
  have fit : 4 * pushes.length + 4 ≤ (s.gpr .esp).toNat := by have := C₁.sp; simp; omega
  cases E with
  | call C E R =>
    cases F with
    | call D F S =>
      rw [call_callEntry, Option.some.injEq] at C D
      subst C D
      have sp : (pushed pushes s).callEntry.gpr .esp = (pushed pushes t).callEntry.gpr .esp := by
        rw [callEntry_esp', callEntry_esp', SP]
      have args : ∀ i < 4, arg (pushed pushes s).callEntry i = arg (pushed pushes t).callEntry i :=
        fun i hi => callEntry_arg_eq (by decide) fit SP RG hi
      have traces := (body_relCT n size hn) _ _ _ _ _ _
        ⟨sp, args, body_readArg E, body_readArg F, entry_self C₁, entry_self C₂⟩ E F
      have r := (ret_gpr R .esp).1
      have q := (ret_gpr S .esp).1
      refine ⟨?_, trivial⟩
      simp only [r, q, State.callEntry_esp, pushed_esp, SP, traces.1]

/-- Two runs about to reduce: the same public stack pointer, working space and
bytes. -/
def CallReady (n : Nat) (s t : State) : Prop :=
  s.gpr .esp = t.gpr .esp ∧ (∀ r ∈ [Reg.ebx, .esi, .edi], s.gpr r = t.gpr r) ∧
    ∃ base size m₁ m₂ p len, VG.Impl.Dsa.Layout.usedBytes ≤ size ∧
      CallIn n m₁ s base size p len ∧ CallIn n m₂ t base size p len

theorem call_relCT (n : Nat) (hn : 0 < n) :
    RelCT isa (CallReady n) (reduceCall n) (fun _ _ => True) := by
  unfold reduceCall
  refine RelCT.seq ?_ (framed_relCT n hn)
  intro s t tr ur sf tf ⟨SP, RG, base, size, m₁, m₂, p, len, _, C₁, C₂⟩ E F
  have W (s : State) : WP isa (.block [.mov .eax (.imm (BitVec.ofNat 32 (contextBytes n / 8)))]) s
      (fun t => Keeps [.eax] s t ∧ t.mem = s.mem ∧ t.gpr .eax = BitVec.ofNat 32 (contextBytes n / 8)) :=
    wp_movS rfl fun _ U _ => WP.block_nil ⟨U.keeps, U.mem, U.gpr⟩
  have K := VG.Proof.Dsa.X86.wp_result (W s) E
  have L := VG.Proof.Dsa.X86.wp_result (W t) F
  refine ⟨?_, ?_⟩
  · cases E with
    | block E => cases F with
      | block F =>
        simp only [execBlock, isa, exec, readSrc, Option.map_some, addrs, srcAddrs, List.map_nil,
          List.nil_append, Option.some.injEq, Prod.mk.injEq] at E F
        exact E.2.symm.trans F.2
  · refine ⟨by rw [K.1.1 .esp (by decide), L.1.1 .esp (by decide)]; exact SP, fun r hr => ?_,
      base, size, m₁, m₂, p, len, C₁.eax K.1 K.2.1, C₂.eax L.1 L.2.1⟩
    simp only [pushes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [K.1.1 _ (by decide), L.1.1 _ (by decide)]; exact RG _ (by simp)
    · rw [K.1.1 _ (by decide), L.1.1 _ (by decide)]; exact RG _ (by simp)
    · rw [K.2.2, L.2.2]
    · rw [K.1.1 _ (by decide), L.1.1 _ (by decide)]; exact RG _ (by simp)

end VG.Proof.Dsa.X86.Red

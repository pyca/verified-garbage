module

public import VerifiedGarbage.Proof.Blowfish.X86.F
public import VerifiedGarbage.Proof.Blowfish.Feistel
import VerifiedGarbage.Proof.Blowfish.X86.Run
import VerifiedGarbage.Proof.Blowfish.Schedule

/-!
# Blowfish on x86 (32-bit): the block function

`cipher_run`: `cipher sch up` takes the halves at `ebp + 16` and `ebp + 20`
to their encryption (`up`) or decryption under the schedule whose address is
at `esp + sch`, changing only `eax`–`edi` but `ebp`, the flags and the
working space's bytes 16–31.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86

open VG VG.X86 VG.Impl.Blowfish.X86 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

/-- The P-array entry of round `m`. -/
def ord (up : Bool) (m : Nat) : Nat := if up then m else 17 - m

/-- The P-array pointer's offset in the schedule after `i` rounds. -/
def pBase (up : Bool) (i : Nat) : Nat := if up then 4096 + 4 * i else 4160 - 4 * i

/-- Byte `d` of the working space at `B`. -/
abbrev slot (B : BitVec 32) (d : Nat) : Addr := B.setWidth 64 + BitVec.ofNat 64 d

theorem addr_slot {B : BitVec 32} (h : B.toNat + 40 ≤ 2 ^ 32) {d : Nat} (hd : d < 40) :
    addr B d = slot B d := addr_of_fit (by omega)

theorem slot_sep (B : BitVec 32) {d e : Nat} (h : d + 4 ≤ e ∨ e + 4 ≤ d) (hd : d < 40) (he : e < 40) :
    Mem.Sep (slot B d) (32 / 8) (slot B e) (32 / 8) :=
  Offset.sep _ h (by omega) (by omega)

/-- What the block function needs: the working space (40 bytes) at `ebp`,
writable and apart from the schedule and the schedule's address, which is at
`esp + sch`. -/
structure CipherEnv (sch : Nat) (S B : BitVec 32) (s : State) : Prop where
  bp : s.gpr .ebp = B
  bfit : B.toNat + 40 ≤ 2 ^ 32
  bw : InRegions s.wr (B.setWidth 64) 40
  schRd : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) sch) 4
  schVal : s.mem.readW (addr (s.gpr .esp) sch) 32 = S
  fit : S.toNat + 4168 ≤ 2 ^ 32
  rd : ∀ o, o + 4 ≤ 4168 → InRegions (s.rd ++ s.wr) (S.setWidth 64 + BitVec.ofNat 64 o) 4
  sepS : Region.Disjoint ⟨B.setWidth 64, 40⟩ ⟨S.setWidth 64, 4168⟩
  sepA : Region.Disjoint ⟨B.setWidth 64, 40⟩ ⟨addr (s.gpr .esp) sch, 4⟩

theorem CipherEnv.slotW {sch : Nat} {S B : BitVec 32} {s : State} (E : CipherEnv sch S B s) {d : Nat}
    (hd : d + 4 ≤ 40) : InRegions s.wr (slot B d) 4 := inRegions_off E.bw hd

theorem CipherEnv.slotR {sch : Nat} {S B : BitVec 32} {s : State} (E : CipherEnv sch S B s) {d : Nat}
    (hd : d + 4 ≤ 40) : InRegions (s.rd ++ s.wr) (slot B d) 4 := region_in (E.slotW hd)

/-- The working space's bytes are apart from the schedule's address. -/
theorem CipherEnv.argSep {sch : Nat} {S B : BitVec 32} {s : State} (E : CipherEnv sch S B s) {d : Nat}
    (hd : d + 4 ≤ 40) : Mem.Sep (addr (s.gpr .esp) sch) 4 (slot B d) 4 :=
  E.sepA.symm.sep (Region.contains_self _ _) (Offset.contains_base _ hd (by omega))

theorem CipherEnv.frame {sch : Nat} {S B : BitVec 32} {s t : State} (E : CipherEnv sch S B s) {rs : List Reg}
    (h : Keep rs s t) (hsp : Reg.esp ∉ rs) (hbp : Reg.ebp ∉ rs)
    (hf : Frame [⟨B.setWidth 64, 40⟩] s.mem t.mem) : CipherEnv sch S B t := by
  have r := keep_reads h
  have esp := h.gpr hsp
  refine ⟨by rw [h.gpr hbp]; exact E.bp, E.bfit, by rw [h.2.2]; exact E.bw, by rw [r, esp]; exact E.schRd,
    ?_, E.fit, fun o ho => by rw [r]; exact E.rd o ho, E.sepS, by rw [esp]; exact E.sepA⟩
  rw [esp, hf.readW (Region.contains_self _ _) (fun r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact E.sepA.symm) (by decide)]
  exact E.schVal

/-- The schedule, after writes to the working space. -/
theorem CipherEnv.sched {sch : Nat} {S B : BitVec 32} {s : State} (E : CipherEnv sch S B s) {m : Mem}
    (hf : Frame [⟨B.setWidth 64, 40⟩] s.mem m) : scheduleAt m (S.setWidth 64) = scheduleAt s.mem (S.setWidth 64) :=
  scheduleAt_eq_of_frame _ hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact E.sepS.symm

theorem CipherEnv.fenv {sch : Nat} {S B : BitVec 32} {s : State} (E : CipherEnv sch S B s) : FEnv sch S s where
  schRd := E.schRd
  schVal := E.schVal
  fit := E.fit
  rd := E.rd
  xl := by rw [E.bp, addr_slot E.bfit (by decide)]; exact E.slotR (by decide)
  fw := by rw [E.bp, addr_slot E.bfit (by decide)]; exact E.slotW (by decide)
  fS := by
    rw [E.bp, addr_slot E.bfit (by decide)]
    exact E.sepS.sub_left (Offset.sub_base _ (by decide))
  fX := by rw [E.bp, addr_slot E.bfit (by decide), addr_slot E.bfit (by decide)]; exact slot_sep B (by decide) (by decide) (by decide)
  fA := by rw [E.bp, addr_slot E.bfit (by decide)]; exact E.argSep (by decide)

theorem round_head (u : State) (up : Bool) {B Pp P : BitVec 32} {a : Addr} (hb : u.gpr .ebp = B)
    (bfit : B.toNat + 40 ≤ 2 ^ 32) (w16 : InRegions u.wr (slot B 16) 4)
    (r28 : InRegions (u.rd ++ u.wr) (slot B 28) 4) (hpp : u.mem.readW (slot B 28) 32 = Pp)
    (ha : addr Pp (pAt up) = a) (hra : InRegions (u.rd ++ u.wr) a 4) (hP : u.mem.readW a 32 = P) :
    WP isa (.block [.mov .ebx (.mem (at_ .ebp ppOff)), .mov .ecx (.mem (at_ .ebx (pAt up))),
        .mov .eax (.mem (at_ .ebp xlOff)), .alu .xor .eax (.reg .ecx), .store (at_ .ebp xlOff) .eax]) u
      fun t => t.mem = u.mem.writeW (slot B 16) (u.mem.readW (slot B 16) 32 ^^^ P) := by
  have r16 := region_in (rs := u.rd) w16
  rw [← ha] at hra hP
  brun [hb, addr_slot bfit, hpp, w16, r16, r28, hra, hP]

/-- Slot 28 and the schedule's address, past the tail's writes of the halves. -/
theorem readW_past2 {m : Mem} {B : BitVec 32} {a : Addr} {n : Nat} (h20 : Mem.Sep a (n / 8) (slot B 20) 4)
    (h16 : Mem.Sep a (n / 8) (slot B 16) 4) (hn : n / 8 < 2 ^ 64) (x y : BitVec 32) :
    ((m.writeW (slot B 20) x).writeW (slot B 16) y).readW a n = m.readW a n := by
  rw [Mem.readW_writeW_sep h16 hn, Mem.readW_writeW_sep h20 hn]

theorem pBase_succ (S : BitVec 32) (up : Bool) {i : Nat} (hi : i < 16) :
    (if up then S + BitVec.ofNat 32 (pBase up i) + 4#32 else S + BitVec.ofNat 32 (pBase up i) - 4#32) =
      S + BitVec.ofNat 32 (pBase up (i + 1)) := by
  cases up
  · simp only [Bool.false_eq_true, ite_false, pBase]
    exact (ofs_sub S (a := 4160 - 4 * i) (b := 4) (by omega)).trans (by congr 2)
  · simp only [ite_true, pBase]
    exact (ofs_add S _ 4).trans (by congr 2)

theorem pBase_end (S : BitVec 32) (up : Bool) {i : Nat} (hi : i < 16) :
    (S - (S + BitVec.ofNat 32 (pBase up (i + 1))) - BitVec.ofNat 32 (2 ^ 32 - if up then pOff + 64 else pOff)
      == 0) = decide (i + 1 = 16) := by
  cases up <;> simp only [pBase, pOff, Bool.false_eq_true, ite_false, ite_true] <;>
  · rw [ofs_neg, ofNat_sub_beq' (by omega) (by decide)]
    congr 1; apply propext; omega

theorem round_tail (u : State) (up : Bool) {sch : Nat} {B S : BitVec 32} {i : Nat} (hi : i < 16)
    (hb : u.gpr .ebp = B) (bfit : B.toNat + 40 ≤ 2 ^ 32) (w16 : InRegions u.wr (slot B 16) 4)
    (w20 : InRegions u.wr (slot B 20) 4) (w24 : InRegions u.wr (slot B 24) 4)
    (w28 : InRegions u.wr (slot B 28) 4)
    (hrs : InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) sch) 4)
    (hs : u.mem.readW (addr (u.gpr .esp) sch) 32 = S)
    (hA : ∀ d, d + 4 ≤ 40 → Mem.Sep (addr (u.gpr .esp) sch) 4 (slot B d) 4)
    (hpp : u.mem.readW (slot B 28) 32 = S + BitVec.ofNat 32 (pBase up i)) :
    WP isa (.block [.mov .eax (.mem (at_ .ebp xrOff)), .alu .xor .eax (.mem (at_ .ebp fOff)),
        .mov .ecx (.mem (at_ .ebp xlOff)), .store (at_ .ebp xrOff) .ecx, .store (at_ .ebp xlOff) .eax,
        .mov .ebx (.mem (at_ .ebp ppOff)), .alu (if up then .add else .sub) .ebx (imm 4),
        .store (at_ .ebp ppOff) .ebx, .mov .ecx (.mem (at_ .esp sch)), .alu .sub .ecx (.reg .ebx),
        .alu .cmp .ecx (imm (2 ^ 32 - if up then pOff + 64 else pOff))]) u fun t =>
      t.mem = ((u.mem.writeW (slot B 20) (u.mem.readW (slot B 16) 32)).writeW (slot B 16)
        (u.mem.readW (slot B 20) 32 ^^^ u.mem.readW (slot B 24) 32)).writeW (slot B 28)
          (S + BitVec.ofNat 32 (pBase up (i + 1))) ∧
      t.zf = some (decide (i + 1 = 16)) := by
  have r16 := region_in (rs := u.rd) w16
  have r20 := region_in (rs := u.rd) w20
  have r24 := region_in (rs := u.rd) w24
  have r28 := region_in (rs := u.rd) w28
  have e28 := fun x y => readW_past2 (m := u.mem) (a := slot B 28) (n := 32)
    (slot_sep B (by decide) (by decide) (by decide)) (slot_sep B (by decide) (by decide) (by decide)) (by decide) x y
  have eA := fun x y => readW_past2 (m := u.mem) (a := addr (u.gpr .esp) sch) (n := 32)
    (hA 20 (by decide)) (hA 16 (by decide)) (by decide) x y
  have eA' : ∀ m : Mem, ∀ x : BitVec 32, (m.writeW (slot B 28) x).readW (addr (u.gpr .esp) sch) 32 =
      m.readW (addr (u.gpr .esp) sch) 32 := fun m x => Mem.readW_writeW_sep (hA 28 (by decide)) (by decide)
  have hp := pBase_succ S up hi
  have he := pBase_end S up hi
  cases up <;>
  · brun [hb, addr_slot bfit, w16, w20, w28, r16, r20, r24, r28, hrs, e28, eA, eA', hs, hpp]
    simp only [ite_false, ite_true, Bool.false_eq_true] at hp he
    rw [hp, he]; exact ⟨rfl, rfl⟩

/-- The address of the P-array entry of round `i`. -/
theorem addr_P {S : BitVec 32} (fit : S.toNat + 4168 ≤ 2 ^ 32) (up : Bool) {i : Nat} (hi : i < 16) :
    addr (S + BitVec.ofNat 32 (pBase up i)) (pAt up) = S.setWidth 64 + BitVec.ofNat 64 (4096 + 4 * ord up i) := by
  unfold addr
  rw [ofs_add, ← addr, addr_of_fit (by cases up <;> simp [pBase, pAt] <;> omega)]
  congr 2; cases up <;> simp [pBase, pAt, ord] <;> omega

/-- The bytes the block function writes: the halves, F and the P-array pointer. -/
abbrev cRegion (B : BitVec 32) : List Region := [⟨slot B 16, 16⟩]

theorem frame_slot {m m' : Mem} {B : BitVec 32} (h : Frame (cRegion B) m m') {d : Nat} (hd : 16 ≤ d)
    (hd' : d + 4 ≤ 32) (v : BitVec 32) : Frame (cRegion B) m (m'.writeW (slot B d) v) :=
  h.writeW (List.mem_singleton_self _) _ (Offset.contains _ hd hd' (by omega))

theorem frame_wide {m m' : Mem} {B : BitVec 32} (h : Frame (cRegion B) m m') :
    Frame [⟨B.setWidth 64, 40⟩] m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩

/-- After `i` rounds from `s₀`. -/
structure CInv (sch : Nat) (S B : BitVec 32) (s₀ : State) (up : Bool) (i : Nat) (u : State) : Prop where
  le : i ≤ 16
  env : CipherEnv sch S B u
  pp : u.mem.readW (slot B 28) 32 = S + BitVec.ofNat 32 (pBase up i)
  halves : (u.mem.readW (slot B 16) 32, u.mem.readW (slot B 20) 32) =
    iter (scheduleAt s₀.mem (S.setWidth 64)) (ord up) i (s₀.mem.readW (slot B 16) 32, s₀.mem.readW (slot B 20) 32)
  keep : Keep lookRegs s₀ u
  frame : Frame (cRegion B) s₀.mem u.mem

theorem round_step {sch : Nat} {S B : BitVec 32} {s₀ : State} (E : CipherEnv sch S B s₀) (up : Bool) {i : Nat}
    (hi : i < 16) {u : State} (I : CInv sch S B s₀ up i u) :
    WP isa (round sch up) u fun u' => CInv sch S B s₀ up (i + 1) u' ∧ u'.zf = some (decide (i + 1 = 16)) := by
  have Eu := I.env
  have fit := E.fit
  have bfit := E.bfit
  have ho : ord up i < 18 := by cases up <;> simp [ord] <;> omega
  let K := scheduleAt s₀.mem (S.setWidth 64)
  have hK : scheduleAt u.mem (S.setWidth 64) = K := E.sched (frame_wide I.frame)
  unfold round
  apply WP.seq
  refine WP.mono (WP.keep [.eax, .ebx, .ecx] (round_head u up (P := pEntry K (ord up i)) Eu.bp bfit
    (Eu.slotW (by decide)) (Eu.slotR (by decide)) I.pp (addr_P fit up hi) (Eu.rd _ (by omega))
    (by rw [← pEntry_read _ _ ho, hK])) (by cases up <;> decide)) fun v ⟨vm, vk⟩ => ?_
  have fv : Frame (cRegion B) s₀.mem v.mem := by rw [vm]; exact frame_slot I.frame (by decide) (by decide) _
  have Ev : CipherEnv sch S B v := Eu.frame vk (by decide) (by decide) (by
    rw [vm]; exact frame_wide (frame_slot (Frame.refl _ _) (by decide) (by decide) _))
  apply WP.seq
  refine WP.mono (f_run Ev.fenv) fun w ⟨wk, wm⟩ => ?_
  rw [Ev.bp, addr_slot bfit (by decide), addr_slot bfit (by decide), E.sched (frame_wide fv)] at wm
  simp only [fOff, xlOff] at wm
  have fw : Frame (cRegion B) s₀.mem w.mem := by rw [wm]; exact frame_slot fv (by decide) (by decide) _
  have Ew : CipherEnv sch S B w := Ev.frame wk (by decide) (by decide) (by
    rw [wm]; exact frame_wide (frame_slot (Frame.refl _ _) (by decide) (by decide) _))
  -- The slots after the head and F.
  have v16 : v.mem.readW (slot B 16) 32 = u.mem.readW (slot B 16) 32 ^^^ pEntry K (ord up i) := by
    rw [vm, Mem.readW_writeW_self32]
  have w16 : w.mem.readW (slot B 16) 32 = u.mem.readW (slot B 16) 32 ^^^ pEntry K (ord up i) := by
    rw [wm, Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide), v16]
  have w20 : w.mem.readW (slot B 20) 32 = u.mem.readW (slot B 20) 32 := by
    rw [wm, Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide), vm,
      Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide)]
  have w24 : w.mem.readW (slot B 24) 32 = f K (u.mem.readW (slot B 16) 32 ^^^ pEntry K (ord up i)) := by
    rw [wm, Mem.readW_writeW_self32, v16]
  have w28 : w.mem.readW (slot B 28) 32 = S + BitVec.ofNat 32 (pBase up i) := by
    rw [wm, Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide), vm,
      Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide), I.pp]
  refine WP.mono (WP.keep [.eax, .ebx, .ecx] (round_tail w up hi Ew.bp bfit (Ew.slotW (by decide))
    (Ew.slotW (by decide)) (Ew.slotW (by decide)) (Ew.slotW (by decide)) Ew.schRd Ew.schVal
    (fun d hd => Ew.argSep hd) w28) (by
      cases up <;> simp [writesOnly, Code.allInstrs, Taint.clobbers, Taint.dst, VG.Proof.MlDsa.X86.Pack.allRegs])) fun x ⟨⟨xm, xz⟩, xk⟩ => ?_
  have fx : Frame (cRegion B) s₀.mem x.mem := by
    rw [xm]
    exact frame_slot (frame_slot (frame_slot fw (by decide) (by decide) _) (by decide) (by decide) _)
      (by decide) (by decide) _
  have Ex : CipherEnv sch S B x := Ew.frame xk (by decide) (by decide) (by
    rw [xm]
    exact frame_wide (frame_slot (frame_slot (frame_slot (Frame.refl _ _) (by decide) (by decide) _)
      (by decide) (by decide) _) (by decide) (by decide) _))
  refine ⟨⟨by omega, Ex, by rw [xm, Mem.readW_writeW_self32], ?_, (((I.keep.trans vk).trans wk).trans xk).mono (by decide), fx⟩, xz⟩
  have x16 : x.mem.readW (slot B 16) 32 = w.mem.readW (slot B 20) 32 ^^^ w.mem.readW (slot B 24) 32 := by
    rw [xm, Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32]
  have x20 : x.mem.readW (slot B 20) 32 = w.mem.readW (slot B 16) 32 := by
    rw [xm, Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]
  rw [x16, x20, w16, w20, w24, iter_succ, ← I.halves]
  simp only [roundStep]
  rw [BitVec.xor_comm]

theorem cipher_start (u : State) (up : Bool) {sch : Nat} {B S : BitVec 32} (hb : u.gpr .ebp = B)
    (bfit : B.toNat + 40 ≤ 2 ^ 32) (w28 : InRegions u.wr (slot B 28) 4)
    (hrs : InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) sch) 4)
    (hs : u.mem.readW (addr (u.gpr .esp) sch) 32 = S) :
    WP isa (.block [.mov .ebx (.mem (at_ .esp sch)), .alu .add .ebx (imm (if up then pOff else pOff + 64)),
        .store (at_ .ebp ppOff) .ebx]) u fun t =>
      t.mem = u.mem.writeW (slot B 28) (S + BitVec.ofNat 32 (pBase up 0)) := by
  cases up <;> brun [hb, addr_slot bfit, w28, hrs, hs, pOff, pBase]

theorem rounds_run {sch : Nat} {S B : BitVec 32} {s : State} (E : CipherEnv sch S B s) (up : Bool) {u : State}
    (I : CInv sch S B s up 0 u) : WP isa (.loop (round sch up) .ne) u (CInv sch S B s up 16) := by
  refine WP.loop (M := isa) (Q := CInv sch S B s up 16)
    (fun (n : Nat) (v : State) => ∃ i, i < 16 ∧ n = 16 - i ∧ CInv sch S B s up i v) ?_ 16 u ⟨0, by decide, rfl, I⟩
  intro n v ⟨i, hi, hn, J⟩
  refine WP.mono (round_step E up hi J) fun v' ⟨J', hz⟩ => ?_
  rw [eval_ne, hz]
  by_cases e : i + 1 = 16
  · left
    exact ⟨by simp [e], e ▸ J'⟩
  · right
    exact ⟨by simp [e], n - 1, by omega, i + 1, by omega, by omega, J'⟩

/-- The addresses of the last P-array entries. -/
theorem addr_last {S : BitVec 32} (fit : S.toNat + 4168 ≤ 2 ^ 32) (up : Bool) :
    addr (S + BitVec.ofNat 32 (pBase up 16)) (pAt up) = S.setWidth 64 + BitVec.ofNat 64 (4096 + 4 * ord up 16) ∧
      addr (S + BitVec.ofNat 32 (pBase up 16)) (4 - pAt up) =
        S.setWidth 64 + BitVec.ofNat 64 (4096 + 4 * ord up 17) := by
  constructor <;>
  · unfold addr
    rw [ofs_add, ← addr, addr_of_fit (by cases up <;> simp [pBase, pAt] <;> omega)]
    congr 2; cases up <;> simp [pBase, pAt, ord]

theorem cipher_end (u : State) (up : Bool) {B Pp P₁₆ P₁₇ : BitVec 32} {a b : Addr} (hb : u.gpr .ebp = B)
    (bfit : B.toNat + 40 ≤ 2 ^ 32) (w16 : InRegions u.wr (slot B 16) 4) (w20 : InRegions u.wr (slot B 20) 4)
    (r28 : InRegions (u.rd ++ u.wr) (slot B 28) 4) (hpp : u.mem.readW (slot B 28) 32 = Pp)
    (ha : addr Pp (pAt up) = a) (hb' : addr Pp (4 - pAt up) = b)
    (hra : InRegions (u.rd ++ u.wr) a 4) (hrb : InRegions (u.rd ++ u.wr) b 4)
    (h16 : u.mem.readW a 32 = P₁₆) (h17 : u.mem.readW b 32 = P₁₇) :
    WP isa (.block [.mov .ebx (.mem (at_ .ebp ppOff)), .mov .ecx (.mem (at_ .ebx (pAt up))),
        .alu .xor .ecx (.mem (at_ .ebp xlOff)), .mov .eax (.mem (at_ .ebx (4 - pAt up))),
        .alu .xor .eax (.mem (at_ .ebp xrOff)), .store (at_ .ebp xlOff) .eax,
        .store (at_ .ebp xrOff) .ecx]) u fun t =>
      t.mem = (u.mem.writeW (slot B 16) (P₁₇ ^^^ u.mem.readW (slot B 20) 32)).writeW (slot B 20)
        (P₁₆ ^^^ u.mem.readW (slot B 16) 32) := by
  have r16 := region_in (rs := u.rd) w16
  have r20 := region_in (rs := u.rd) w20
  rw [← ha] at hra h16
  rw [← hb'] at hrb h17
  brun [hb, addr_slot bfit, hpp, w16, w20, r16, r20, r28, hra, hrb, h16, h17]

/-- The block function. -/
theorem cipher_run {sch : Nat} {S B : BitVec 32} {s : State} (E : CipherEnv sch S B s) (up : Bool) :
    WP isa (cipher sch up) s fun t =>
      (t.mem.readW (slot B 16) 32, t.mem.readW (slot B 20) 32) =
        feistel (scheduleAt s.mem (S.setWidth 64)) (ord up) (s.mem.readW (slot B 16) 32)
          (s.mem.readW (slot B 20) 32) ∧
      Keep lookRegs s t ∧ Frame (cRegion B) s.mem t.mem := by
  have fit := E.fit
  have bfit := E.bfit
  unfold cipher
  apply WP.seq
  refine WP.mono (WP.keep [.ebx] (cipher_start s up E.bp bfit (E.slotW (by decide)) E.schRd E.schVal) (by
    cases up <;> simp [writesOnly, Code.allInstrs, Taint.clobbers, Taint.dst, VG.Proof.MlDsa.X86.Pack.allRegs]))
    fun u ⟨um, uk⟩ => ?_
  have fu : Frame (cRegion B) s.mem u.mem := by rw [um]; exact frame_slot (Frame.refl _ _) (by decide) (by decide) _
  have I0 : CInv sch S B s up 0 u := by
    refine ⟨by decide, E.frame uk (by decide) (by decide) (frame_wide fu), by rw [um, Mem.readW_writeW_self32], ?_,
      uk.mono (by decide), fu⟩
    rw [um, Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide)]
    rfl
  apply WP.seq
  refine WP.mono (rounds_run E up I0) fun v V => ?_
  obtain ⟨a16, a17⟩ := addr_last fit up
  have Ev := V.env
  let K := scheduleAt s.mem (S.setWidth 64)
  have hK : scheduleAt v.mem (S.setWidth 64) = K := E.sched (frame_wide V.frame)
  have r16 : 4096 + 4 * ord up 16 + 4 ≤ 4168 := by cases up <;> decide
  have r17 : 4096 + 4 * ord up 17 + 4 ≤ 4168 := by cases up <;> decide
  have o16 : ord up 16 < 18 := by cases up <;> decide
  have o17 : ord up 17 < 18 := by cases up <;> decide
  refine WP.mono (WP.keep [.eax, .ebx, .ecx] (cipher_end v up (P₁₆ := pEntry K (ord up 16))
    (P₁₇ := pEntry K (ord up 17)) Ev.bp bfit (Ev.slotW (by decide)) (Ev.slotW (by decide))
    (Ev.slotR (by decide)) V.pp a16 a17 (Ev.rd _ r16) (Ev.rd _ r17)
    (by rw [← pEntry_read _ _ o16, hK]) (by rw [← pEntry_read _ _ o17, hK])) (by
      cases up <;> decide))
    fun t ⟨tm, tk⟩ => ?_
  refine ⟨?_, (V.keep.trans tk).mono (by decide), by
    rw [tm]; exact frame_slot (frame_slot V.frame (by decide) (by decide) _) (by decide) (by decide) _⟩
  rw [tm, Mem.readW_writeW_sep (slot_sep B (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self32, Mem.readW_writeW_self32, feistel_eq, ← V.halves, BitVec.xor_comm,
    BitVec.xor_comm (pEntry _ _)]

end VG.Proof.Blowfish.X86

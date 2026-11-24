module

public import VerifiedGarbage.Proof.Ffdh.X86.Checks
public import VerifiedGarbage.Proof.Ffdh.X86.Stages
public import VerifiedGarbage.Proof.Ffdh.Lead
import VerifiedGarbage.Proof.Ffdh.X86.KeyScan
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Import
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Rsa.X86.StackTactic
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Stage

/-!
# FFDH on i686: a power to q, over its bytes from the first nonzero one

`qScan_ok`: the scan leaves, in the header's words `qpOff` and `qlOff`, the
address of q's first nonzero byte (of its last byte, if all are zero) and
the number of bytes from it on, `lead` of q's bytes past q's address and
short of `p_len` (`Proof/Ffdh/Lead.lean`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.QPower

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86 VG.Proof.Ffdh
open VG.Impl.Ffdh.X86
open VG.Proof.Ffdh.X86.KeyScan (wp_movzx8 word_room bytesAt_getD)

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- q's bytes: the domain's third component. -/
abbrev qBytes (m : Mem) (args : Nat → BitVec 32) (len : Nat) : List Byte :=
  Spec.Rsa.bytesAt m (byteAddr (args 2) + BitVec.ofNat 64 (2 * len)) len

/-- The carry of `n + 0xFFFFFFFE`: whether `n` is at least two. -/
theorem carry_two {n : Nat} (hn : n < 2 ^ 31) :
    decide (2 ^ 32 ≤ (BitVec.ofNat 32 n).toNat + (0xFFFFFFFE : BitVec 32).toNat) = decide (2 ≤ n) := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  show decide (2 ^ 32 ≤ n + 4294967294) = _
  by_cases h : 2 ≤ n
  · rw [decide_eq_true h, decide_eq_true (by omega_arith)]
  · rw [decide_eq_false h, decide_eq_false (by omega_arith)]

/-- Before byte `i` of q. -/
structure ScanAt (s : State) (len i : Nat) (args : Nat → BitVec 32) (u : State) : Prop where
  esi : u.gpr .esi = args 6 + BitVec.ofNat 32 i
  ecx : u.gpr .ecx = BitVec.ofNat 32 (len - i)
  mem : u.mem = s.mem
  keeps : Keeps [.eax, .ecx, .edx, .esi] s u

/-- One byte of the scan: on to the next while it is before `lead`, and ZF set at `lead`. -/
theorem qScanStep_ok (G : DomGeo args base bytes len (3 * len) s.rd s.wr) {i : Nat} {u : State}
    (hi : i ≤ lead (qBytes s.mem args len)) (I : ScanAt s len i args u) :
    WP isa (.block qScanStep) u fun v =>
      ScanAt s len (if i < lead (qBytes s.mem args len) then i + 1 else i) args v ∧
      v.zf = some (decide (¬ i < lead (qBytes s.mem args len))) := by
  have fit := G.fit
  have lw := G.lower
  have up := G.upper
  obtain ⟨a6, n6⟩ : byteAddr (args 6) = byteAddr (args 2) + BitVec.ofNat 64 (2 * len) ∧
      (args 6).toNat = (args 2).toNat + 2 * len := G.addr (k := 2) (by decide) (by omega_arith)
  generalize hbs : qBytes s.mem args len = bs at hi ⊢
  obtain bl : bs.length = len := by rw [← hbs]; exact VG.Proof.Bignum.bytesAt_length _ _ _
  obtain ne : bs ≠ [] := fun e => by rw [e] at bl; simp at bl; omega_arith
  obtain ll := lead_lt ne
  obtain il : i < len := by omega_arith
  -- The byte.
  obtain ea : u.ea ⟨.esi, 0⟩ = byteAddr (args 2) + BitVec.ofNat 64 (2 * len) + BitVec.ofNat 64 i := by
    change addr (u.gpr .esi) 0 = _
    rw [I.esi, addr_eq (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith), BitVec.add_zero, ← a6]
    exact addr_eq (by omega_arith)
  obtain rdB : InRegions (u.rd ++ u.wr)
      (byteAddr (args 2) + BitVec.ofNat 64 (2 * len) + BitVec.ofNat 64 i) 1 := by
    rw [I.keeps.2.1, I.keeps.2.2, VG.Offset.add_add]
    exact VG.CallLay.inRegions_sub G.rd (by omega_arith) (by omega_arith)
  obtain byte : u.mem (byteAddr (args 2) + BitVec.ofNat 64 (2 * len) + BitVec.ofNat 64 i) = bs.getD i 0 := by
    rw [← hbs, I.mem, bytesAt_getD _ _ il]
  generalize hb : bs.getD i 0 = b at byte
  obtain bi : bs[i]'(by omega_arith) = b := by rw [← hb, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega_arith), Option.getD_some]
  refine wp_movzx8 ea rdB fun u1 a1 => ?_
  refine wp_addS rfl fun u2 a2 c2 => ?_
  refine wp_sbbS rfl c2 fun u3 a3 _ => ?_
  refine wp_logicS (.inr rfl) rfl fun u4 a4 => ?_
  refine wp_movS rfl fun u5 a5 _ => ?_
  refine wp_addS rfl fun u6 a6' c6 => ?_
  refine wp_sbbS rfl c6 fun u7 a7 _ => ?_
  refine wp_logicS (.inl rfl) rfl fun u8 a8 => ?_
  refine wp_logicS (.inl rfl) rfl fun u9 a9 => ?_
  refine wp_addS rfl fun u10 a10 _ => ?_
  refine wp_subS rfl fun u11 a11 _ => ?_
  refine wp_testS rfl fun v T z => WP.block_nil ?_
  obtain E4 : u4.gpr .eax = cmask (!(b != 0)) := by
    rw [a4.gpr, ite_eq_right (by decide), a3.gpr, KeyScan.sbb_self, a1.gpr, byte, KeyScan.carry_ne, KeyScan.cmask_not]
  obtain X5 : u5.gpr .edx = BitVec.ofNat 32 (len - i) := by
    rw [a5.gpr, a4.other _ (by decide), a3.other _ (by decide), a2.other _ (by decide), a1.other _ (by decide), I.ecx]
  obtain E7 : u7.gpr .edx = cmask (decide (2 ≤ len - i)) := by
    rw [a7.gpr, KeyScan.sbb_self, X5, carry_two (by omega_arith)]
  generalize hc : (!(b != 0) && decide (2 ≤ len - i)) = c
  obtain E9 : u9.gpr .eax = BitVec.ofNat 32 c.toNat := by
    rw [a9.gpr, ite_eq_left rfl, a8.gpr, ite_eq_left rfl, a7.other _ (by decide), a6'.other _ (by decide),
      a5.other _ (by decide), E4, E7, KeyScan.cmask_and, hc]
    exact cmask_and_one c
  obtain cl : c = decide (i < lead bs) := by
    rw [← hc]
    by_cases h : i < lead bs
    · obtain ⟨_, z⟩ := lead_zero i h
      rw [decide_eq_true h, show b = 0 by rw [← bi]; exact z, decide_eq_true (by omega_arith)]
      rfl
    · rw [decide_eq_false h]
      obtain e : i = lead bs := by omega_arith
      by_cases hl : lead bs + 1 < bs.length
      · obtain nz : b ≠ 0 := by rw [← bi]; subst e; exact lead_nonzero ne hl
        rw [show (b != 0) = true from bne_iff_ne.mpr nz]
        rfl
      · rw [decide_eq_false (by omega_arith), Bool.and_false]
  obtain K : Keeps [.eax, .ecx, .edx, .esi] u v :=
    ((((((((((((a1.keeps.mono (by decide) : Keeps [.eax, .ecx, .edx, .esi] u u1).widen a2.keeps).widen
      a3.keeps).widen a4.keeps).widen a5.keeps).widen a6'.keeps).widen a7.keeps).widen a8.keeps).widen
      a9.keeps).widen a10.keeps).widen a11.keeps).widen (T.keeps []))
  obtain M : v.mem = s.mem := by
    rw [T.mem, a11.mem, a10.mem, a9.mem, a8.mem, a7.mem, a6'.mem, a5.mem, a4.mem, a3.mem, a2.mem, a1.mem, I.mem]
  obtain esi9 : u9.gpr .esi = args 6 + BitVec.ofNat 32 i := by
    rw [a9.other _ (by decide), a8.other _ (by decide), a7.other _ (by decide), a6'.other _ (by decide),
      a5.other _ (by decide), a4.other _ (by decide), a3.other _ (by decide), a2.other _ (by decide),
      a1.other _ (by decide), I.esi]
  obtain ecx10 : u10.gpr .ecx = BitVec.ofNat 32 (len - i) := by
    rw [a10.other _ (by decide), a9.other _ (by decide), a8.other _ (by decide), a7.other _ (by decide),
      a6'.other _ (by decide), a5.other _ (by decide), a4.other _ (by decide), a3.other _ (by decide),
      a2.other _ (by decide), a1.other _ (by decide), I.ecx]
  obtain eax11 : u11.gpr .eax = BitVec.ofNat 32 c.toNat := by
    rw [a11.other _ (by decide), a10.other _ (by decide), E9]
  refine ⟨⟨?_, ?_, M, I.keeps.trans K⟩, ?_⟩
  · rw [congrFun T.gpr .esi, a11.other _ (by decide), a10.gpr, esi9, E9, cl, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    by_cases h : i < lead bs
    · rw [decide_eq_true h, ite_eq_left h]; rfl
    · rw [decide_eq_false h, ite_eq_right h]; rfl
  · rw [congrFun T.gpr .ecx, a11.gpr, ecx10, a10.other _ (by decide), E9, cl]
    by_cases h : i < lead bs
    · rw [decide_eq_true h, ite_eq_left h,
        BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by show 1 ≤ len - i; omega_arith)]
      congr 1
    · rw [decide_eq_false h, ite_eq_right h]
      exact BitVec.sub_zero _
  · rw [z, eax11, cl]
    by_cases h : i < lead bs
    · rw [decide_eq_true h, decide_eq_false (fun n => n h)]; rfl
    · rw [decide_eq_false h, decide_eq_true h]; rfl

/-- What `qScan` leaves in the header, for q's bytes `bs`: the address of the first byte that counts,
and the bytes from it on. -/
structure QAt (base : Addr) (len : Nat) (args : Nat → BitVec 32) (bs : List Byte) (m : Mem) : Prop where
  ptr : m.readW (off base qpOff) 32 = args 6 + BitVec.ofNat 32 (lead bs)
  cnt : m.readW (off base qlOff) 32 = BitVec.ofNat 32 (len - lead bs)

/-- The scan: the header's two words, and nothing else of the memory. -/
theorem qScan_ok (h : In Ex base bytes len args s) (G : DomGeo args base bytes len (3 * len) s.rd s.wr) :
    WP isa qScan s fun u => Step Ex base bytes len args s u ∧
      QAt base len args (qBytes s.mem args len) u.mem ∧ Kept base len [] [qpOff, qlOff] s.mem u.mem := by
  have lw := G.lower
  obtain r1 := word_room h (d := qpOff) (by decide)
  obtain r2 := word_room h (d := qlOff) (by decide)
  generalize hbs : qBytes s.mem args len = bs
  unfold qScan qScanInit
  refine WP.seq (wp_movS (h.arg (i := 6) (by decide)) fun u1 a1 _ => ?_)
  obtain h1 := h.regs a1.keeps a1.mem
  refine wp_movS (h1.arg (i := 7) (by decide)) fun u2 a2 _ => WP.block_nil ?_
  obtain I0 : ScanAt s len 0 args u2 :=
    ⟨by rw [a2.other _ (by decide), a1.gpr]; exact (BitVec.add_zero _).symm, by rw [a2.gpr, G.e7]; rfl,
      by rw [a2.mem, a1.mem], (a1.keeps.mono (by decide) : Keeps [.eax, .ecx, .edx, .esi] s u1).widen a2.keeps⟩
  refine WP.seq (WP.mono (WP.loop (M := isa) (Q := ScanAt s len (lead bs) args)
    (fun n u => ∃ i, n = lead bs - i ∧ i ≤ lead bs ∧ ScanAt s len i args u) ?_ (lead bs) u2
    ⟨0, rfl, Nat.zero_le _, I0⟩) fun u3 I3 => ?_)
  · rintro n u ⟨i, rfl, hi, I⟩
    refine WP.mono (qScanStep_ok G (by rw [hbs]; exact hi) I) fun v ⟨Iv, z⟩ => ?_
    rw [hbs] at Iv z
    obtain he : isa.eval .ne v = some (!decide (¬ i < lead bs)) := by
      show v.zf.map (!·) = _; rw [z]; rfl
    by_cases hl : i < lead bs
    · rw [ite_eq_left hl] at Iv
      exact .inr ⟨by rw [he, decide_eq_false (fun n => n hl)]; rfl, lead bs - (i + 1), by omega_arith, i + 1, rfl,
        by omega_arith, Iv⟩
    · rw [ite_eq_right hl] at Iv
      obtain e : i = lead bs := by omega_arith
      exact .inl ⟨by rw [he, decide_eq_true hl]; rfl, e ▸ Iv⟩
  -- The two words.
  obtain S₃ : Step Ex base bytes len args s u3 := Step.regs h I3.mem I3.keeps
  obtain s3 : Scr u3 base bytes := h.scratch.of_keeps I3.keeps (by decide)
  unfold qScanEnd
  refine wp_storeS (s3.ea (d := qpOff) (by omega_arith)) (s3.write (d := qpOff) (n := 4) r1) fun u4 m4 => ?_
  obtain s4 : Scr u4 base bytes := s3.of_keeps (m4.keeps []) (by decide)
  refine wp_storeS (s4.ea (d := qlOff) (by omega_arith)) (s4.write (d := qlOff) (n := 4) r2) fun u5 m5 =>
    WP.block_nil ?_
  obtain O4 : Outside base qpOff 4 u3.mem u4.mem := by rw [m4.mem]; exact writeW32_outside _ _ _ (by decide)
  obtain S₄ : Step Ex base bytes len args u3 u4 := Step.word S₃.inp (by decide) O4 (m4.keeps [])
  obtain O5 : Outside base qlOff 4 u4.mem u5.mem := by rw [m5.mem]; exact writeW32_outside _ _ _ (by decide)
  obtain S₅ : Step Ex base bytes len args u4 u5 := Step.word S₄.inp (by decide) O5 (m5.keeps [])
  refine ⟨(S₃.trans S₄).trans S₅, ⟨?_, ?_⟩, ?_⟩
  · rw [m5.mem, Mem.readW_writeW_sep (Offset.sep base (by decide) (by decide) (by decide)) (by decide), m4.mem,
      Mem.readW_writeW_self32, I3.esi]
  · rw [m5.mem, Mem.readW_writeW_self32, congrFun m4.gpr .ecx, I3.ecx]
  · rw [← I3.mem]
    exact ((kept_word S₃.inp (d := qpOff) (by decide) (by decide) O4).mono (by decide) (by decide)).trans
      ((kept_word S₄.inp (d := qlOff) (by decide) (by decide) O5).mono (by decide) (by decide))

/-- q's bytes after a stage. -/
theorem qBytes_keep (h : In Ex base bytes len args s) {rd wr : List Region}
    (G : DomGeo args base bytes len (3 * len) rd wr) {sp : BitVec 32} (RF : RoomF sp base bytes)
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), 3 * len⟩ (below sp 176)) {m m' : Mem}
    (F : Frame (frameF base sp (fR len)) m m') : qBytes m' args len = qBytes m args len := by
  have up := G.upper
  exact frame_bytes F (fun r hr => (dom_frame h G RF hb40 r hr).sub_left (Offset.sub_base _ (by omega_arith)))
    (by omega_arith)

/-- The scan's words through what keeps the header's words. -/
theorem QAt.kept {bs : List Byte} {m m' : Mem} {js ds : List Nat} (Q : QAt base len args bs m)
    (k : Kept base len js ds m m') (hp : qpOff ∉ ds := by decide) (hl : qlOff ∉ ds := by decide) :
    QAt base len args bs m' :=
  ⟨(BitVec.eq_of_toNat_eq (k.words qpOff (by decide) (by decide) (by decide) hp)).trans Q.ptr,
    (BitVec.eq_of_toNat_eq (k.words qlOff (by decide) (by decide) (by decide) hl)).trans Q.cnt⟩

/-- A header word through changes in the 176 bytes below `sp` alone. -/
theorem frameF_word {t : State} (h : In Ex base bytes len args t) {sp : BitVec 32} (RF : RoomF sp base bytes)
    {m m' : Mem} (F : Frame (frameF base sp []) m m') {d : Nat} (hd : d + 4 ≤ 32) :
    m'.readW (off base d) 32 = m.readW (off base d) 32 := by
  have r := word_room h hd
  apply BitVec.eq_of_toNat_eq
  show w32 m' base d = w32 m base d
  rw [← w32_val32_one, ← w32_val32_one]
  exact frameF_val32 F RF h.scratch.nowrap (by omega_arith) (fun _ h => nomatch h) (fun _ h => nomatch h)

/-- The bytes of a number from byte `a` on. -/
theorem drop_bytes (m : Mem) (p : Addr) {a n : Nat} (h : a ≤ n) :
    Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 a) (n - a) = (Spec.Rsa.bytesAt m p n).drop a := by
  rw [← VG.Proof.Dsa.bytesAt_slice m p (total := n) (offset := a) (len := n - a) (by omega_arith),
    List.take_of_length_le (by simp only [List.length_drop, VG.Proof.Bignum.bytesAt_length]; exact Nat.le_refl _)]

/-- The arguments with q's address and length, from its first byte that counts, in 10 and 11. -/
def qArgs (args : Nat → BitVec 32) (p l : BitVec 32) (i : Nat) : BitVec 32 :=
  if i = 10 then p else if i = 11 then l else args i

/-- `setQ`, in the callee's frame: its arguments 10 and 11 are the header's two words. -/
theorem setQ_ok {u : State} (h : In Ex base bytes len args s) (RF : RoomF (s.gpr .esp) base bytes)
    (hu : In (fun _ _ => True) base bytes len args u) (CI : CalleeIn s u) :
    WP isa (.block setQ) u fun v => Keeps [.eax] u v ∧
      Frame [⟨(u.gpr .esp).setWidth 64, 76⟩] u.mem v.mem ∧
      In (fun _ _ => True) base bytes len
        (qArgs args (u.mem.readW (off base qpOff) 32) (u.mem.readW (off base qlOff) 32)) v := by
  have top := hu.top
  obtain r1 := word_room hu (d := qpOff) (by decide)
  obtain r2 := word_room hu (d := qlOff) (by decide)
  generalize hP : (u.gpr .esp).setWidth 64 = P
  obtain vals : ∀ i < 18, u.mem.readW (slotAddr P i) 32 = args i := fun i hi => by
    rw [← hP, ← (hu.stack i hi).value]
    show _ = u.mem.readW (VG.Proof.Dsa.X86.stackAddress u i) 32
    rw [show VG.Proof.Dsa.X86.stackAddress u i = slotAddr ((u.gpr .esp).setWidth 64) i from
      addr_eq (by omega_arith)]
  obtain fa : Region.Disjoint ⟨P, 76⟩ ⟨base, bytes⟩ := by rw [← hP]; exact callee_frame_apart RF CI.esp
  unfold setQ
  refine wp_movS (readSrc_sc hu.scratch r1) fun u1 a1 _ => ?_
  obtain ⟨ea1, w1⟩ := frame76_store (t := u1) (P := P) (by rw [a1.other _ (by decide), hP])
    (by rw [a1.other _ (by decide)]; exact top)
    (by rw [a1.keeps.2.2, CI.wr, hP]; exact List.mem_cons_self ..) (i := 10) (by decide)
  refine wp_storeS ea1 w1 fun u2 m2 => ?_
  obtain K2 : Keeps [.eax] u u2 := a1.keeps.trans ((m2.keeps []).mono (by decide))
  obtain F2 : Frame [⟨P, 76⟩] u.mem u2.mem := by
    rw [m2.mem, a1.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  refine wp_movS ((readSrc_sc (hu.scratch.of_keeps K2 (by decide) (by decide)) r2).trans (congrArg some
    (F2.readW (r := ⟨off base qlOff, 4⟩) (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (fa.sub_right (Offset.sub_base _ r2)).symm) (by decide))))
    fun u3 a3 _ => ?_
  obtain K3 : Keeps [.eax] u u3 := K2.trans a3.keeps
  obtain ⟨ea3, w3⟩ := frame76_store (t := u3) (P := P) (by rw [K3.1 _ (by decide), hP])
    (by rw [K3.1 _ (by decide)]; exact top)
    (by rw [K3.2.2, CI.wr, hP]; exact List.mem_cons_self ..) (i := 11) (by decide)
  refine wp_storeS ea3 w3 fun v m4 => WP.block_nil ?_
  obtain K4 : Keeps [.eax] u v := K3.trans ((m4.keeps []).mono (by decide))
  obtain mv : v.mem = ((u.mem.writeW (slotAddr P 10) (u.mem.readW (off base qpOff) 32)).writeW (slotAddr P 11)
      (u.mem.readW (off base qlOff) 32)) := by rw [m4.mem, a3.mem, a3.gpr, m2.mem, a1.mem, a1.gpr]
  refine ⟨K4, ?_, in_calleeOf h RF ((K4.1 _ (by decide)).trans CI.esp) ((K4.1 _ (by decide)).trans CI.edi)
    (K4.2.1.trans CI.rd) (by rw [K4.2.2, CI.wr, K4.1 _ (by decide)]) rfl rfl rfl fun i hi => ?_⟩
  · rw [mv]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by decide) (by decide))
  · rw [K4.1 _ (by decide), hP, mv]
    unfold qArgs
    by_cases e11 : i = 11
    · subst e11; rw [Mem.readW_writeW_self32]; rfl
    · rw [frame76_other _ _ _ (fun e => e11 e.symm) (by decide) hi, ite_eq_right e11]
      by_cases e10 : i = 10
      · subst e10; rw [Mem.readW_writeW_self32]; rfl
      · rw [frame76_other _ _ _ (fun e => e10 e.symm) (by decide) hi, ite_eq_right e10, vals i hi]

theorem winQBody_noSp :
    NoSp (.seq (.block ((List.range 18).flatMap copyArg)) (.seq (.block setQ)
      (.seq (loadTop (.slot .wide 8) (one .wide) 10 11) (windowPowerWith .wide (lenCount 11)))) : Prog isa) :=
  NoSp.of_all (by rsa_stack_shape)

/-- `winQCall`: slot 5 to the power of q, raised over q's bytes from its first that counts, for the scan's
words. -/
theorem winQCall_ok {M : Nat} (C : CtxOk Ex base bytes len args .wide M s)
    (G : DomGeo args base bytes len (3 * len) s.rd s.wr) (RF : RoomF (s.gpr .esp) base bytes)
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), 3 * len⟩ (below (s.gpr .esp) 176))
    (h3 : sv s.mem base len .wide 3 = 1) (h4 : sv s.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % M)
    (Q : QAt base len args (qBytes s.mem args len) s.mem) :
    WP isa winQCall s fun u => CtxOk Ex base bytes len args .wide M u ∧
      Frame (frameF base (s.gpr .esp) (pwR len .wide)) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u ∧
      sv u.mem base len .wide 6 = sv s.mem base len .wide 5 ^ comp s.mem args len 2 % M := by
  have fit := G.fit
  have lw := G.lower
  have up := G.upper
  obtain lb := len_le_bc len
  obtain bw := bc_eq_cwc len .wide
  obtain f8 := C.inp.slot_fit .wide (j := 8) (by decide)
  have blt := C.inp.bytes_lt
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  obtain ⟨a6, n6⟩ : byteAddr (args 6) = byteAddr (args 2) + BitVec.ofNat 64 (2 * len) ∧
      (args 6).toNat = (args 2).toNat + 2 * len := G.addr (k := 2) (by decide) (by omega_arith)
  obtain qv : comp s.mem args len 2 = Spec.Rsa.os2ip (qBytes s.mem args len) := rfl
  generalize hbs : qBytes s.mem args len = bs at Q qv
  obtain bl : bs.length = len := by rw [← hbs]; exact VG.Proof.Bignum.bytesAt_length _ _ _
  obtain ne : bs ≠ [] := fun e => by rw [e] at bl; simp at bl; omega_arith
  obtain ll := lead_lt ne
  unfold winQCall
  refine WP.mono (argCall_okW winQBody_noSp C.inp RF (pwR_fit C.inp .wide)
    (R := WinMem base len M (sv s.mem base len .wide 5 ^ comp s.mem args len 2 % M))
    (fun W F hr => winMem_below C.inp RF W F hr) fun u hu Fs CI => ?_)
    fun w ⟨I, F, K, a, b, c⟩ => ⟨⟨I, a, C.gt, C.odd, b⟩, F, K, c⟩
  -- The callee's arguments 10 and 11.
  refine WP.seq (WP.mono (setQ_ok C.inp RF hu CI) fun v ⟨Kv, Fv, hv⟩ => ?_)
  rw [frameF_word C.inp RF Fs (d := qpOff) (by decide), Q.ptr,
    frameF_word C.inp RF Fs (d := qlOff) (by decide), Q.cnt] at hv
  generalize hA : qArgs args (args 6 + BitVec.ofNat 32 (lead bs)) (BitVec.ofNat 32 (len - lead bs)) = A at hv
  obtain e10 : A 10 = args 6 + BitVec.ofNat 32 (lead bs) := by rw [← hA]; rfl
  obtain e11 : A 11 = BitVec.ofNat 32 (len - lead bs) := by rw [← hA]; rfl
  obtain n10 : (A 10).toNat = (args 2).toNat + 2 * len + lead bs := by
    rw [e10, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith
  obtain ea : byteAddr (A 10) = byteAddr (args 2) + BitVec.ofNat 64 (2 * len + lead bs) := by
    rw [e10, VG.Proof.Bignum.X86.byteAddr_add (by omega_arith), a6, VG.Offset.add_add]
  obtain vesp : v.gpr .esp = u.gpr .esp := Kv.1 _ (by decide)
  obtain Fs' : Frame (frameF base (s.gpr .esp) []) s.mem v.mem :=
    Fs.trans (frameF_of_sub Fv fun r hr => by rw [List.mem_singleton.mp hr]; exact CI.sub)
  have e := fun j (hj : j ≤ 27) => frameF_sv C.inp RF Fs' hj
  obtain Cv : CtxOk (fun _ _ => True) base bytes len A .wide M v :=
    ⟨hv, by rw [e 0 (by decide)]; exact C.mod, C.gt, C.odd, by rw [frameF_inv C.inp RF Fs']; exact C.inv⟩
  -- q's bytes from the first that counts.
  obtain rdq : InRegions (v.rd ++ v.wr) (byteAddr (A 10)) (len - lead bs) := by
    obtain ⟨r, hr, hc⟩ := VG.CallLay.inRegions_sub (off := 2 * len + lead bs) (l := len - lead bs) G.rd
      (by omega_arith) (by omega_arith)
    rw [ea, Kv.2.1, Kv.2.2, CI.rd, CI.wr]
    refine ⟨r, ?_, hc⟩
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  obtain qsub : Region.Sub ⟨byteAddr (A 10), len - lead bs⟩ ⟨byteAddr (args 2), 3 * len⟩ := by
    rw [ea]; exact Offset.sub_base _ (by omega_arith)
  refine WP.seq (WP.mono (loadTopCtx_ok Cv (d := 8) (p := 10) (l := 11) (L := len - lead bs) (by decide) (by decide)
    (by decide) (by decide) e11 (by omega_arith) (by omega_arith) (by omega_arith) rdq (G.apart.sub_left qsub))
    fun u₁ ⟨C₁, V₁, O₁, K₁⟩ => ?_)
  obtain qb : Spec.Rsa.bytesAt v.mem (byteAddr (A 10)) (len - lead bs) = bs.drop (lead bs) := by
    rw [frame_bytes Fs' (fun r hr => by
      simp only [frameF, frameR, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hb40.sub_left qsub
      · exact (hb40.sub_left qsub).sub_right (VG.X86.below_sub (by decide) RF.low)) (by omega_arith), ea,
      ← VG.Offset.add_add]
    subst hbs
    exact drop_bytes _ _ (by omega_arith)
  rw [qb, os2ip_drop_lead, ← qv] at V₁
  obtain sp₁ : u₁.gpr .esp = u.gpr .esp := (K₁.1 _ (by decide)).trans vesp
  refine WP.mono (windowPowerWith_ok C₁
    (by rw [slotKeep hv (by decide) (by decide) O₁, e 3 (by decide)]; exact h3)
    (by rw [slotKeep hv (by decide) (by decide) O₁, e 4 (by decide)]; exact h4) (N := 2 * (len - lead bs))
    (by omega_arith) (by omega_arith) fun t Ct =>
    wp_movS (Ct.inp.arg (i := 11) (by decide)) fun t₁ a₁ _ => wp_addS rfl fun t₂ a₂ _ => WP.block_nil
      ⟨a₁.keeps.trans (a₂.keeps.mono (by decide)), by rw [a₂.mem, a₁.mem], by
        rw [a₂.gpr, a₁.gpr, e11, BitVec.ofNat_add_ofNat]; congr 1; omega_arith⟩)
    fun w ⟨Cw, F, K, Y⟩ => ⟨?_, (Kv.mono (by decide) : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] u v).trans
      (K₁.trans K), Cw.mod, Cw.inv, ?_⟩
  · rw [sp₁] at F
    exact ((Fv.sub fun r hr => ⟨r, by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self .., fun _ h => h⟩).trans
      ((frameR_of_outside (sp := u.gpr .esp) (ws := pwR len .wide) O₁ (by omega_arith) (by simp)).sub
        fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)).trans
      (F.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
  · rw [Y, V₁, show 32 * cwc len .wide = 8 * bc len .wide by omega_arith, top_windows (by omega_arith),
      slotKeep hv (by decide) (by decide) O₁, e 5 (by decide)]

/-- Slot 6 the wide slot `b` to the power of q, modulo p (in the wide slot 9), for the scan's words. -/
theorem powQ_ok (h : In Ex base bytes len args s) (G : DomGeo args base bytes len (3 * len) s.rd s.wr)
    (RF : RoomF (s.gpr .esp) base bytes)
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), 3 * len⟩ (below (s.gpr .esp) 176)) {P b : Nat} (hb9 : 9 ≤ b)
    (hb : b ≤ 19) (hP : safeM (sv s.mem base len .wide 9) = P)
    (Q : QAt base len args (qBytes s.mem args len) s.mem) :
    WP isa (powQ b) s fun u =>
      CtxOk Ex base bytes len args .wide P u ∧
      sv u.mem base len .wide 6 = sv s.mem base len .wide b ^ comp s.mem args len 2 % P ∧
      sv u.mem base len .wide 3 = 1 ∧
      Frame (frameF base (s.gpr .esp) (stR len 0)) s.mem u.mem ∧ Kept base len [] [] s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have bl := h.bytes_lt
  have lw := G.lower
  obtain f8 := h.slot_fit .wide (j := 8) (by decide)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  obtain e5 := lo_wide len 5
  obtain e8 := lo_wide len 8
  have nb : numBase = 3336 := rfl
  unfold powQ
  refine WP.seq (WP.mono (ctxP_ok h RF hP) fun u₁ ⟨C₁, one₁, R₁, F₁, k₁, K₁⟩ => ?_)
  have h₁ := C₁.inp
  refine WP.seq (WP.mono (copyIn_ok h₁ (j := b) (d := 5) hb9 hb (by decide)) fun u₂ ⟨O₂, V₂, K₂⟩ => ?_)
  obtain C₂ : CtxOk Ex base bytes len args .wide P u₂ := by
    refine C₁.keepF (regs := [.eax, .ebx, .ecx, .edx, .ebp]) K₂ (by decide) (by decide)
      (ws := [(lo len (.slot .wide 5), bc len .wide)]) (frameR_of_outside O₂ (by omega_arith) (by simp)) ?_ ?_
    · intro p hp; simp only [List.mem_singleton] at hp; subst hp; dsimp only; omega_arith
    · intro p hp; simp only [List.mem_singleton] at hp; subst hp; dsimp only; omega_arith
  obtain G₂ : Frame (frameR base (s.gpr .esp) (stR len 0)) u₁.mem u₂.mem :=
    stR_of_outside h (by decide) O₂ ⟨_, by simp, slot_in h .wide (j := 5) (by decide)⟩
  obtain F₂ : Frame (frameF base (s.gpr .esp) (stR len 0)) s.mem u₂.mem := F₁.trans (frameF_of G₂)
  obtain S₂ : Step Ex base bytes len args s u₂ := Step.opsF h RF F₂ (K₁.trans (K₂.mono (by decide)))
  obtain k₂ : Kept base len [] [] s.mem u₂.mem := k₁.trans (kept_ops h G₂ h.room)
  obtain sp₂ : u₂.gpr .esp = s.gpr .esp := S₂.esp
  obtain qb : qBytes u₂.mem args len = qBytes s.mem args len := qBytes_keep h G RF hb40 S₂.frame
  obtain one₂ : sv u₂.mem base len .wide 3 = 1 := by rw [slotKeep h₁ (by decide) (by decide) O₂, one₁]
  refine WP.mono (winQCall_ok C₂ (G.keep ⟨rfl, rfl⟩ S₂.keeps) (by rw [sp₂]; exact RF) (by rw [sp₂]; exact hb40) one₂
    (by rw [slotKeep h₁ (by decide) (by decide) O₂, R₁]) (by rw [qb]; exact Q.kept k₂)) fun u ⟨C, F, K, Y⟩ => ?_
  rw [V₂, k₁.slots b hb9 hb (by simp), comp_keep h G RF hb40 S₂.frame (k := 2) (by omega_arith)] at Y
  rw [sp₂] at F
  obtain Gf := frameF_widen F (pwR_in C₂.inp .wide 0)
  exact ⟨C, Y, by rw [pwR_sv3 C₂.inp F RF, one₂], F₂.trans Gf, k₂.trans (keptF_ops h Gf RF), S₂.keeps.trans K⟩

end VG.Proof.Ffdh.X86.QPower

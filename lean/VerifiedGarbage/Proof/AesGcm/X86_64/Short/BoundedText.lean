module
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Seal
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Impl.AesGcm.X86_64.Short

/-! Seal the two public spans of a bounded record using one source/destination kernel. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.Short
open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short
open VG.Spec.Aes (bytesAt)

structure SpanPair (s : State) (P Q D G : Addr) (m n : Nat) : Prop where
  first : m ≤ n
  left : s.gpr .rbx = P
  right : s.gpr .r12 = Q
  size : s.gpr .rbp = BitVec.ofNat 64 m
  readLeft : Covers [⟨P, m⟩] (s.rd ++ s.wr)
  leftAlias : P = D ∨ (⟨P, m⟩ : Region).Disjoint ⟨D,n⟩
  leftStage : (⟨P,m⟩ : Region).Disjoint ⟨G,n⟩
  readRight : m < n → Covers [⟨Q,n-m⟩] (s.rd ++ s.wr)
  rightAlias : m < n → Q = D + BitVec.ofNat 64 m ∨ (⟨Q,n-m⟩ : Region).Disjoint ⟨D,n⟩
  rightStage : m < n → (⟨Q,n-m⟩ : Region).Disjoint ⟨G,n⟩

/-- After both spans, the ciphertext is the XOR of the logical plaintext
with one contiguous keystream, even when a span ends inside a block. -/
theorem xb_spans (mem : Mem) (P Q K : Addr) (m n : Nat) (hm : m ≤ n) :
    xb mem P K m ++ xb mem Q (K + BitVec.ofNat 64 m) (n-m) =
      List.zipWith (· ^^^ ·) (bytesAt mem P m ++ bytesAt mem Q (n-m)) (bytesAt mem K n) := by
  rw [show bytesAt mem K n = bytesAt mem K m ++ bytesAt mem (K + BitVec.ofNat 64 m) (n-m) by
    rw [← bytesAt_add, Nat.add_sub_of_le hm]]
  exact (List.zipWith_append (by rw [length_bytesAt, length_bytesAt])).symm

private theorem xorLeft_pre {s t : State} {D K G : Addr} {m n : Nat} (xp : XorPre true s D K G n)
    (le : m ≤ n) (si : t.gpr .rsi = D) (dx : t.gpr .rdx = K) (di : t.gpr .rdi = G)
    (cx : t.gpr .rcx = BitVec.ofNat 64 m) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : XorPre true t D K G m := by
  have sub (a : Addr) := @Region.sub_prefix a m n le
  refine ⟨si, dx, di, cx, Nat.lt_of_le_of_lt le xp.lt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rd,wr]; exact covers_prefix xp.rS le
  · rw [rd,wr]; exact covers_prefix xp.rK le
  · rw [wr]; exact covers_prefix xp.wS le
  · intro hg; rw [wr]; exact covers_prefix (xp.wD hg) le
  · exact (xp.dSK.sub_left (sub D)).sub_right (sub K)
  · exact fun hg => ((xp.dSD hg).sub_left (sub D)).sub_right (sub G)
  · exact fun hg => ((xp.dKD hg).sub_left (sub K)).sub_right (sub G)

private theorem xorRight_pre {s t : State} {D K G : Addr} {m n : Nat} (xp : XorPre true s D K G n)
    (le : m ≤ n) (si : t.gpr .rsi = D + BitVec.ofNat 64 m) (dx : t.gpr .rdx = K + BitVec.ofNat 64 m)
    (di : t.gpr .rdi = G + BitVec.ofNat 64 m) (cx : t.gpr .rcx = BitVec.ofNat 64 (n-m))
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) :
    XorPre true t (D + BitVec.ofNat 64 m) (K + BitVec.ofNat 64 m) (G + BitVec.ofNat 64 m) (n-m) := by
  have bound : m + (n-m) ≤ n := by omega_using [le]
  have low : n < 2^64 := by omega_using [xp.lt]
  have sub (a : Addr) := Offset.sub_base a bound
  refine ⟨si, dx, di, cx, Nat.lt_of_le_of_lt (Nat.sub_le _ _) xp.lt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rd,wr]; exact covers_off xp.rS bound low
  · rw [rd,wr]; exact covers_off xp.rK bound low
  · rw [wr]; exact covers_off xp.wS bound low
  · intro hg; rw [wr]; exact covers_off (xp.wD hg) bound low
  · exact (xp.dSK.sub_left (sub D)).sub_right (sub K)
  · exact fun hg => ((xp.dSD hg).sub_left (sub D)).sub_right (sub G)
  · exact fun hg => ((xp.dKD hg).sub_left (sub K)).sub_right (sub G)

private abbrev Kept (s t : State) := ∀ r ∈ [Reg.r13,.r14,.r15,.rsp], t.gpr r = s.gpr r

set_option linter.unusedSimpArgs false in
theorem boundedText_ok {s : State} {P Q D K G : Addr} {m n : Nat}
    (xp : XorPre true s D K G n) (hs : SpanPair s P Q D G m n) :
    WP isa boundedText s (TextDone s D G
      (List.zipWith (· ^^^ ·) (bytesAt s.mem P m ++ bytesAt s.mem Q (n-m)) (bytesAt s.mem K n))) := by
  have hm := hs.first
  have hn : n < 2^64 := by omega_using [xp.lt]
  have hm64 : m < 2^64 := Nat.lt_of_le_of_lt hm hn
  rw [← xb_spans _ _ _ _ _ _ hm]
  unfold boundedText
  refine WP.seq ?_
  let t := (s.setReg .r11 (s.gpr .rcx)).setReg .rcx (s.gpr .rbp)
  have pre : XorPre true t D K G m := xorLeft_pre xp hm xp.rsi xp.rdx xp.rdi hs.size rfl rfl
  have first := xorText_at_ok true .rbx t pre hs.left (by decide) hs.readLeft
    (hs.leftAlias.imp_right (fun h => h.sub_right (Region.sub_prefix hm)))
    (fun _ => hs.leftStage.sub_right (Region.sub_prefix hm))
  refine WP.of_runBlock ⟨t, by xrun [], WP.seq (WP.mono first ?_)⟩
  rintro u ⟨mu, regs, rd, wr, z⟩
  change u.mem = xw true s.mem D G (xb s.mem P K m) at mu
  have r11 : u.gpr .r11 = BitVec.ofNat 64 n := (regs _ (by decide) (by decide) (by decide) (by decide)).trans xp.rcx
  have bp : u.gpr .rbp = BitVec.ofNat 64 m := (regs _ (by decide) (by decide) (by decide) (by decide)).trans hs.size
  have keep : Kept s u := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact regs _ (by decide) (by decide) (by decide) (by decide)
  obtain ⟨v, run, cnt, zf, unchanged, mv, rv, wv, zv⟩ :
      ∃ v, runBlock isa [.mov .rcx (.reg .r11), .alu .sub .rcx (.reg .rbp)] u = some v ∧
        v.gpr .rcx = BitVec.ofNat 64 (n-m) ∧ v.zf = some (decide (n=m)) ∧
        (∀ r, r ≠ .rcx → v.gpr r = u.gpr r) ∧ v.mem = u.mem ∧ v.rd = u.rd ∧ v.wr = u.wr ∧ ZKeep [] u v := by
    refine ⟨_, by xrun [] <;> rfl, ?_⟩
    refine ⟨?_, ?_, ?_, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩
    · simp only [gpr_setReg, ite_true, gpr_arithFlags, r11, bp]
      exact ofNat_sub hm hn
    · simp only [zf_arithFlags, gpr_setReg, ite_true, reduceCtorEq, ite_false, r11, bp]
      exact congrArg some (sub_beq hn hm64)
    · intro r hr; simp [gpr_setReg, hr]
  refine WP.seq (WP.of_runBlock ⟨v, run, WP.ite (decide (n=m)) (by simpa [eval] using zf) ?_ ?_⟩)
  · intro he; have eq := of_decide_eq_true he; subst m
    refine WP.block_nil ?_
    refine ⟨?_, ?_, rv.trans rd, wv.trans wr, ?_⟩
    · rw [mv, mu]; simp [xb, bytesAt]
    · intro r hr; rw [unchanged r (by simp at hr; rcases hr with rfl|rfl|rfl|rfl <;> decide), keep r hr]
    · exact (z.trans (zv.mono (by simp)))
  · intro he
    have positive : m < n := Nat.lt_of_le_of_ne hm (Ne.symm (of_decide_eq_false he))
    have usi : u.gpr .rsi = D := (regs _ (by decide) (by decide) (by decide) (by decide)).trans xp.rsi
    have udx : u.gpr .rdx = K := (regs _ (by decide) (by decide) (by decide) (by decide)).trans xp.rdx
    have udi : u.gpr .rdi = G := (regs _ (by decide) (by decide) (by decide) (by decide)).trans xp.rdi
    have ur12 : u.gpr .r12 = Q := (regs _ (by decide) (by decide) (by decide) (by decide)).trans hs.right
    obtain ⟨w, args, si, dx, di, ptr, gr, mw, rw', ww, zw⟩ :
        ∃ w, runBlock isa [.mov .rbx (.reg .r12), .alu .add .rsi (.reg .rbp),
            .alu .add .rdx (.reg .rbp), .alu .add .rdi (.reg .rbp)] v = some w ∧
          w.gpr .rsi = D + BitVec.ofNat 64 m ∧ w.gpr .rdx = K + BitVec.ofNat 64 m ∧
          w.gpr .rdi = G + BitVec.ofNat 64 m ∧ w.gpr .rbx = Q ∧
          (∀ r, r ≠ .rbx → r ≠ .rsi → r ≠ .rdx → r ≠ .rdi → w.gpr r = v.gpr r) ∧
          w.mem = v.mem ∧ w.rd = v.rd ∧ w.wr = v.wr ∧ ZKeep [] v w := by
      refine ⟨_, by xrun [] <;> rfl, ?_⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩
      · simp [gpr_setReg, unchanged .rsi (by decide), unchanged .rbp (by decide), usi, bp]
      · simp [gpr_setReg, unchanged .rdx (by decide), unchanged .rbp (by decide), udx, bp]
      · simp [gpr_setReg, unchanged .rdi (by decide), unchanged .rbp (by decide), udi, bp]
      · simp [gpr_setReg, unchanged .r12 (by decide), ur12]
      · intro r h₁ h₂ h₃ h₄; simp [gpr_setReg, *]
    have rightPre := xorRight_pre xp hm si dx di ((gr _ (by decide) (by decide) (by decide) (by decide)).trans cnt)
      (rw'.trans (rv.trans rd)) (ww.trans (wv.trans wr))
    have over : Q = D + BitVec.ofNat 64 m ∨ (⟨Q,n-m⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 m,n-m⟩ :=
      (hs.rightAlias positive).imp_right fun h => h.sub_right (Offset.sub_base _ (by omega_using [hm]))
    have right := xorText_at_ok true .rbx w rightPre ptr (by decide)
      (by rw [rw',ww,rv,wv,rd,wr]; exact hs.readRight positive) over
      (fun _ => (hs.rightStage positive).sub_right (Offset.sub_base _ (by omega_using [hm])))
    refine WP.seq (WP.of_runBlock ⟨w,args,WP.mono right ?_⟩)
    rintro x ⟨mx,gx,rx,wx,zx⟩
    have len := length_xb s.mem P K m
    have dstPrefix : (⟨Q,n-m⟩ : Region).Disjoint ⟨D,m⟩ := by
      rcases hs.rightAlias positive with rfl|sep
      · exact Offset.disjoint_base _ (Nat.le_refl _) (by omega_using [hm,hn])
      · exact sep.sub_right (Region.sub_prefix hm)
    have framed : Frame [⟨D,m⟩,⟨G,m⟩] s.mem w.mem := by
      rw [mw,mv,mu]
      simpa only [len] using xw_frame true s.mem D G (xb s.mem P K m)
    have same (z : Addr) (hd : (⟨z,n-m⟩ : Region).Disjoint ⟨D,m⟩)
        (hg : (⟨z,n-m⟩ : Region).Disjoint ⟨G,m⟩) :=
      bytesAt_frame framed (p := z) (n := n-m) (fun r hr => by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl <;> with_reducible assumption) (by omega_using [hn])
    have eq : xb w.mem Q (K + BitVec.ofNat 64 m) (n-m) = xb s.mem Q (K + BitVec.ofNat 64 m) (n-m) := by
      unfold xb
      rw [same Q dstPrefix ((hs.rightStage positive).sub_right (Region.sub_prefix hm)),
        same _ ((xp.dSK.symm.sub_left (Offset.sub_base _ (by omega_using [hm]))).sub_right (Region.sub_prefix hm))
          (((xp.dKD rfl).sub_left (Offset.sub_base _ (by omega_using [hm]))).sub_right (Region.sub_prefix hm))]
    refine ⟨?_, ?_, rx.trans (rw'.trans (rv.trans rd)), wx.trans (ww.trans (wv.trans wr)), ?_⟩
    · rw [mx,eq,mw,mv,mu]
      have glue := xw_append true s.mem (S:=D) (D:=G) (n:=n) (xb s.mem P K m)
        (xb s.mem Q (K + BitVec.ofNat 64 m) (n-m)) xp.lt (by simp [length_xb]; omega_using [hm]) xp.dSD
      simpa only [length_xb] using glue
    · intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl <;>
        rw [gx _ (by decide) (by decide) (by decide) (by decide),
          gr _ (by decide) (by decide) (by decide) (by decide), unchanged _ (by decide), keep _ (by simp)]
    · exact (((z.trans (zv.mono (by simp))).trans (zw.mono (by simp))).trans zx)

abbrev spanRegs : List Reg := [.rbx,.rbp,.r12,.rsi,.rdx,.rdi,.rcx]

theorem boundedText_rel : RelCT isa (fun s t => ∀ r ∈ spanRegs, s.gpr r = t.gpr r)
    boundedText (fun _ _ => True) :=
  rel_taint spanRegs (fun _ _ h => h) ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.X86_64.Short

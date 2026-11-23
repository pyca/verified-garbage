module

public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.FragmentStep
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
public import VerifiedGarbage.Proof.AesGcm.AArch64.Crypt
import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Loop
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.Gcm.SealGather

/-! Bytewise out-of-place XOR at either end of a descriptor. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather.Generic

open VG VG.AArch64 VG.AArch64.RegUpd VG.WriteBytes VG.Impl.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64 (xorBytes)

abbrev byteRegs : List Reg := [.x13,.x14,.x23,.x11,.x26,.x24,.x10]
abbrev xorStep : List Instr :=
  [.ldrb .x13 .x23 0, .ldrb .x14 .x11 0, .logic .eor .w .x13 .x13 .x14,
   .strb .x13 .x26 0, ptr .x23 .x23 1, ptr .x11 .x11 1, ptr .x26 .x26 1,
   .subImm .x .x24 .x24 1, .subImm .x .x10 .x10 1]

structure ByteAt (s : State) (S K D : Addr) (n rem i : Nat) (t : State) : Prop
    extends Fragment.Kept s t byteRegs where
  mem : t.mem = writeBytes s.mem D (xorBytes s.mem S K i)
  src : t.gpr .x23 = S + BitVec.ofNat 64 i
  key : t.gpr .x11 = K + BitVec.ofNat 64 i
  dst : t.gpr .x26 = D + BitVec.ofNat 64 i
  count : t.gpr .x10 = BitVec.ofNat 64 (n-i)
  rest : t.gpr .x24 = BitVec.ofNat 64 (rem-i)

theorem byte_start {s : State} {S K D : Addr} {n rem : Nat}
    (hs : s.gpr .x23 = S) (hk : s.gpr .x11 = K) (hd : s.gpr .x26 = D)
    (hc : s.gpr .x10 = BitVec.ofNat 64 n) (hr : s.gpr .x24 = BitVec.ofNat 64 rem) :
    ByteAt s S K D n rem 0 s := by
  exact ⟨⟨fun _ _ => rfl,rfl,rfl,rfl⟩, by simp [xorBytes, Spec.Aes.bytesAt, writeBytes_nil],
    by simpa using hs, by simpa using hk, by simpa using hd, hc, hr⟩

set_option linter.unusedSimpArgs false in
theorem step_ok {s t : State} {S K D : Addr} {n rem i : Nat}
    (a : ByteAt s S K D n rem i t) (hs : LoopPre s S D n) (hk : LoopPre s K D n)
    (hi : i < n) (hr : n ≤ rem) :
    WP isa (.block xorStep) t (ByteAt s S K D n rem (i+1)) := by
  have hn := hs.lt
  have rs := in_of_covers hs.rd hi (by omega_arith)
  have rk := in_of_covers hk.rd hi (by omega_arith)
  have wd := in_of_covers hs.wr hi (by omega_arith)
  have hlen := length_xorBytes s.mem S K i
  apply WP.of_runBlock
  simp only [xorStep, ptr, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load,
    State.store, State.read, Size.bits, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self,
    ↓reduceIte, BitVec.add_zero, gpr_write, rd_write, wr_write, mem_write, reduceCtorEq,
    BitVec.setWidth_eq, a.src, a.key, a.dst, a.rd, a.wr, rs, rk, wd, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r he => ?_, a.sp, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [byteRegs,List.mem_cons,List.not_mem_nil,or_false,not_or] at he
    simp [gpr_write, he.1, he.2.1, he.2.2.1, he.2.2.2.1, he.2.2.2.2.1, he.2.2.2.2.2.1, he.2.2.2.2.2.2]
    exact a.gpr r (by simpa [byteRegs] using he)
  · simp only [mem_write, byte_xor, read_one, a.mem, src_kept hs.disj hi hn _ hlen,
      src_kept hk.disj hi hn _ hlen, xorBytes_succ, writeBytes_snoc _ _ _ _ (by rw [hlen]; omega_arith), hlen]
    rfl
  all_goals simp only [gpr_write, reduceCtorEq, ite_true, ite_false, State.read, Size.bits,
      BitVec.setWidth_eq, a.src,a.key,a.dst,a.rest,a.count,BitVec.add_assoc,succ_ofNat]
  all_goals first | exact congrArg _ (succ_ofNat i) | rw [Offset.ofNat_sub_ofNat (by omega_arith)]; rfl

theorem xorBytes_ok {s : State} {S K D : Addr} {n rem : Nat}
    (a : ByteAt s S K D n rem 0 s) (hs : LoopPre s S D n) (hk : LoopPre s K D n)
    (hr : n ≤ rem) :
    WP isa Impl.AesGcm.AArch64.DirectGather.xorBytes s (ByteAt s S K D n rem n) := by
  have hn := hs.lt
  refine WP.ite (decide (n = 0)) (eval_zero a.count (by omega_arith)) (fun he => ?_) (fun hne => ?_)
  · have he' : n = 0 := of_decide_eq_true he
    subst n
    exact WP.of_runBlock ⟨_,rfl,a⟩
  · refine WP.loop (M := isa) (body := .block xorStep) (c := .nonzero .x .x10)
      (fun k t => ∃ i, k = n-i ∧ i < n ∧ ByteAt s S K D n rem i t)
      ?_ n s ⟨0,rfl,by simp at hne; omega_arith,a⟩
    rintro k t ⟨i,rfl,hi,h⟩
    refine (step_ok h hs hk hi hr).mono fun u hu => ?_
    have ev := eval_nonzero hu.count (by omega_arith)
    by_cases e : i+1 = n
    · left; exact ⟨by rw [ev,e]; simp, e ▸ hu⟩
    · right; exact ⟨by rw [ev]; simp; omega_arith, n-(i+1), by omega_arith, i+1,rfl,by omega_arith,hu⟩

end VG.Proof.AesGcm.AArch64.DirectGather.Generic

/-! Full-block CTR-to calls followed by the final partial block of a descriptor. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather.Generic

open VG VG.AArch64 VG.AArch64.RegUpd VG.WriteBytes VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)
open VG.Proof.Gcm (Ctr xorKs)
variable {Wn : Nat} {Ctx St W SP : Addr} {k : Reg → BitVec 64} {R P : Nat} {icb : Block}
  {D O : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}

structure Encrypted (Wn : Nat) (Ctx St W SP : Addr) (k : Reg → BitVec 64) (R : Nat) (icb : Block)
    (P : Nat) (D O : Addr) (n : Nat) (m₀ : Mem) (t : State) : Prop where
  env : Env Wn Ctx St W SP t
  kept : KeptTo k t
  src : t.gpr .x23 = D + BitVec.ofNat 64 n
  dst : t.gpr .x26 = O + BitVec.ofNat 64 n
  rest : t.gpr .x24 = 0
  offset : t.gpr .x25 = BitVec.ofNat 64 ((P+n)%16)
  ctr : Ctr t.mem (St + 48) (St + 64) (ciphOf m₀ Ctx R) icb (P+n)
  out : bytesAt t.mem O n = xorKs (ciphOf m₀ Ctx R) icb P (bytesAt m₀ D n)
  frame : Frame (crFrame Wn St W O n) m₀ t.mem

set_option linter.unusedSimpArgs false in
theorem directTail_ok (h : Cr3G Wn true Ctx St W SP k R icb P D O n m₀ j s)
    (hc : Ctr m₀ (St + 48) (St + 64) (ciphOf m₀ Ctx R) icb P) (hpos : n-j ≠ 0) :
    WP isa (.seq (.block [mov .x10 .x24, mov .x25 .x24, ptr .x11 .x20 64])
        Impl.AesGcm.AArch64.DirectGather.xorBytes) s (Encrypted Wn Ctx St W SP k R icb P D O n m₀) := by
  have data : DataOk Wn St W s D n := h.data
  obtain ⟨hw,hd,x26⟩ := h.outAt
  have hj := h.le
  have hn := data.lt
  have ht := h.lt16
  have rem := hw.drop h.le
  have kd := (rem.ok.st.sub_right (Lay.stSub (d := 64) (by omega_arith : 64 + (n-j) ≤ 80))).symm
  have sd := (hd.sub_left (Offset.sub_base D (d := j) (n := n-j) (by omega_arith))).sub_right
    (Offset.sub_base O (d := j) (n := n-j) (by omega_arith))
  obtain ⟨t,run,x10,x25,x11,g⟩ : ∃ t, runBlock isa [mov .x10 .x24, mov .x25 .x24, ptr .x11 .x20 64] s =
      some t ∧ t.gpr .x10 = BitVec.ofNat 64 (n-j) ∧ t.gpr .x25 = BitVec.ofNat 64 (n-j) ∧
      t.gpr .x11 = St + BitVec.ofNat 64 64 ∧ Regs [.x10,.x25,.x11] s t := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write,h.x24], by simp [gpr_write,h.x24],
      by simp [gpr_write,h.env.x20], ⟨by others_tac,rfl,rfl,rfl,rfl⟩⟩
  refine WP.seq (WP.of_runBlock ⟨t,run,?_⟩)
  have ls : LoopPre t (D + BitVec.ofNat 64 j) (O + BitVec.ofNat 64 j) (n-j) :=
    ⟨by omega_arith, by rw [g.rd,g.wr]; exact (data.drop h.le).rd, by rw [g.wr]; exact rem.wr, sd⟩
  have lk : LoopPre t (St+BitVec.ofNat 64 64) (O + BitVec.ofNat 64 j) (n-j) :=
    ⟨by omega_arith, by rw [g.rd,g.wr]; exact covers_left (h.env.perm.stC (by omega_arith)), ls.wr, kd⟩
  refine (xorBytes_ok (byte_start ((g.others _ (by decide)).trans h.x23) x11
    ((g.others _ (by decide)).trans x26) x10 ((g.others _ (by decide)).trans h.x24)) ls lk (Nat.le_refl _)).mono
    fun u a => ?_
  have hmem := a.mem
  rw [g.mem] at hmem
  have hlen := length_xorBytes s.mem (D + BitVec.ofNat 64 j) (St + BitVec.ofNat 64 64) (n-j)
  have fw : Frame [⟨O + BitVec.ofNat 64 j,n-j⟩] s.mem u.mem := by rw [hmem]; exact writeBytes_frame' _ hlen
  have keyFrame (o : Nat) (ho : o + 16 ≤ 80) :=
    blockAt_frame fw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (rem.ok.st.sub_right (Lay.stSub ho)).symm)
      (p := St + BitVec.ofNat 64 o)
  obtain ⟨mc,hmc,hks,hcb⟩ := h.ctr1 hpos hc
  have hw0 := h.whole.resolve_left hpos
  obtain ⟨hbytes,hctr⟩ := Proof.Gcm.ctr_tail hmc hw0 hks hcb (d := bytesAt s.mem (D + BitVec.ofNat 64 j) (n-j))
    (by rw [length_bytesAt]; omega_arith) (by rw [length_bytesAt]; omega_arith)
  rw [length_bytesAt] at hbytes hctr
  have hprefix := bytesAt_frame fw (p := O) (n := j) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact split_disj h.le hn) (by omega_arith)
  have htail : bytesAt u.mem (O + BitVec.ofNat 64 j) (n-j) = xorKs (ciphOf m₀ Ctx R) icb (P+j)
      (bytesAt m₀ (D + BitVec.ofNat 64 j) (n-j)) := by
    have e := bytesAt_writeBytes_self s.mem (O + BitVec.ofNat 64 j) _ (by rw [hlen]; omega_arith)
    rw [hlen] at e
    rw [hmem,e,xorBytes,hbytes,h.rest]
  have kept : ∀ r ∈ [Reg.x19,.x20,.x21,.x22,.x27,.x28], u.gpr r = s.gpr r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;> exact (a.gpr _ (by decide)).trans (g.others _ (by decide))
  refine ⟨h.env.keep (fun r hr => kept r (by simpa using List.mem_append_left [.x22,.x27,.x28] hr))
    (a.sp.trans g.sp) (a.rd.trans g.rd) (a.wr.trans g.wr), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    exact (kept r (List.mem_append_right [Reg.x19,.x20,.x21] hr)).trans (h.kept r hr)
  · rw [a.src,Offset.add_add, Nat.add_sub_of_le hj]
  · rw [a.dst,Offset.add_add, Nat.add_sub_of_le hj]
  · rw [a.rest,Nat.sub_self]; rfl
  · rw [a.gpr _ (by decide),x25]; congr 1; omega_arith
  · rw [show P+n = P+j+(n-j) by omega_arith]
    exact hctr.congr (keyFrame 48 (by decide)) (keyFrame 64 (by decide))
  · rw [show n = j+(n-j) by omega_arith]
    exact done_append (hprefix.trans (h.done hc)) htail
  · exact h.frame.trans (fw.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr
                                               exact ⟨_,List.mem_cons_self ..,Offset.sub_base O (by omega_arith)⟩)

theorem aligned_ok (L : Lay Wn Ctx St W) (v : GcmImpl) (h : CrInG Wn true Ctx St W SP k R P D O n s)
    (hP : P % 16 = 0) (hc : Ctr s.mem (St+48) (St+64) (ciphOf s.mem Ctx R) icb P)
    (hv : v.ctr.scratch ≤ Wn - 512) :
    WP isa (Impl.AesGcm.AArch64.DirectGather.aligned v.callees) s
      (Encrypted Wn Ctx St W SP k R icb P D O n s.mem) := by
  have ciph {m' : Mem} (f : Frame (crFrame Wn St W O n) s.mem m') :=
    ciph_frame f (ctx_crFrame L (OutAt.dataW h.outAt h.data)) h.rounds
  refine WP.seq ((crArgsG_ok L true (h.mid (icb := icb) hP)).mono fun s₁ h₁ =>
    WP.seq ((ctrCallG1_ok L v h₁ (ciph h₁.frame) hv).mono fun t ⟨ht,hlt⟩ => ?_))
  refine WP.ite (decide (n - (0+16*((n-0)/16)) = 0)) (eval_zero ht.x24 (by omega_arith)) (fun e => ?_) (fun e => ?_)
  · have he := of_decide_eq_true e
    have eqn : 0+16*((n-0)/16) = n := by omega_arith
    rw [eqn] at ht
    exact WP.of_runBlock ⟨_,rfl,⟨ht.env,ht.kept,ht.x23,ht.outAt.2.2,
      by rw [ht.x24,Nat.sub_self]; rfl,by rw [ht.x25]; congr 1; omega_arith,ht.ctr hc,ht.done hc,ht.frame⟩⟩
  · have he := of_decide_eq_false e
    exact WP.seq ((crSeg2_ok L ht hlt).mono fun s₃ h₃ => WP.seq
      ((ctrCall2_ok L v h₃ (ciph h₃.frame) hv).mono fun _ h₄ => directTail_ok h₄ hc he))

end VG.Proof.AesGcm.AArch64.DirectGather.Generic

/-! Consume only the still-unused bytes of the preceding counter block. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather.Generic

open VG VG.AArch64 VG.AArch64.RegUpd VG.WriteBytes VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)
open VG.Proof.Gcm (Ctr xorKs)

structure Head (Wn : Nat) (Ctx St W SP : Addr) (k : Reg → BitVec 64) (R : Nat) (icb : Block)
    (P : Nat) (D O : Addr) (n j : Nat) (s t : State) : Prop where
  env : Env Wn Ctx St W SP t
  kept : KeptTo k t
  x22 : t.gpr .x22 = BitVec.ofNat 64 R
  src : t.gpr .x23 = D + BitVec.ofNat 64 j
  dst : t.gpr .x26 = O + BitVec.ofNat 64 j
  rest : t.gpr .x24 = BitVec.ofNat 64 (n-j)
  offset : t.gpr .x25 = BitVec.ofNat 64 ((P+j)%16)
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  ctr : Ctr t.mem (St+48) (St+64) (ciphOf s.mem Ctx R) icb (P+j)
  out : bytesAt t.mem O j = xorKs (ciphOf s.mem Ctx R) icb P (bytesAt s.mem D j)
  frame : Frame [⟨O,j⟩] s.mem t.mem

theorem leftover_ok {Wn : Nat} {Ctx St W SP : Addr} {k : Reg → BitVec 64} {R P : Nat} {icb : Block}
    {D O : Addr} {n : Nat} {s : State} (h : CrInG Wn true Ctx St W SP k R P D O n s)
    (hc : Ctr s.mem (St+48) (St+64) (ciphOf s.mem Ctx R) icb P) :
    WP isa Impl.AesGcm.AArch64.DirectGather.leftover s (Head Wn Ctx St W SP k R icb P D O n (crHead (P%16) n) s) := by
  have data : DataOk Wn St W s D n := h.data
  obtain ⟨hw,hd,x26⟩ := h.outAt
  simp at x26
  have hn := data.lt
  refine WP.ite (decide (P % 16 = 0)) (eval_zero h.x25 (by omega_arith)) (fun e => ?_) (fun e => ?_)
  · have he := of_decide_eq_true e
    simp only [crHead,he,ite_true]
    exact WP.of_runBlock ⟨_,rfl,⟨h.env,h.kept,h.x22,by simpa using h.x23,by simpa using x26,h.x24,by simpa using h.x25,rfl,rfl,by simpa using hc,rfl,Frame.refl _ _⟩⟩
  have hoff := of_decide_eq_false e
  simp only [crHead,hoff,ite_false]
  let j := min (16-P%16) n
  have hj : j ≤ n := Nat.min_le_right ..
  have hspace : P%16+j ≤ 16 := by dsimp [j]; omega_arith
  refine WP.seq ((minK_ok s h.x25 h.x24 (by omega_arith) hn).mono fun s₁ ⟨x10,g,m,sp,rd,wr⟩ => ?_)
  obtain ⟨t,run,x11,x25,reg⟩ : ∃ t, runBlock isa [ptr .x11 .x20 64,.add .x .x11 .x11 .x25,
      .add .x .x25 .x25 .x10,imm .x9 15,.logic .and .x .x25 .x25 .x9] s₁ = some t ∧
      t.gpr .x11 = St + BitVec.ofNat 64 (64+P%16) ∧ t.gpr .x25 = BitVec.ofNat 64 ((P+j)%16) ∧
      Regs [.x11,.x25,.x9] s₁ t := by
    refine ⟨_,by arun [],?_⟩
    refine ⟨?_,?_,⟨by others_tac,rfl,rfl,rfl,rfl⟩⟩
    · simp [gpr_write,g .x20 (by decide),g .x25 (by decide),h.env.x20,h.x25,Offset.add_add]
    · simp only [gpr_write,ite_true,ite_false,reduceCtorEq,g .x25 (by decide),h.x25,x10,BitVec.setWidth_eq]
      rw [show BitVec.setWidth 64 (15#16) <<< (16*0) = BitVec.ofNat 64 15 by decide,and15,← BitVec.ofNat_add]
      change BitVec.ofNat 64 ((BitVec.ofNat 64 (P%16+j)).toNat %16) = _
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show P%16+j < 2^64 by omega_arith)]
      congr 1; omega_arith
  refine WP.seq (WP.of_runBlock ⟨t,run,?_⟩)
  have tr := reg.rd.trans rd
  have tw := reg.wr.trans wr
  have tm := reg.mem.trans m
  have ls : LoopPre t D O j := ⟨by omega_arith, by rw [tr,tw]; exact (data.take hj).rd,
    by rw [tw]; exact (hw.take hj).wr, (hd.sub_left (Region.sub_prefix hj)).sub_right (Region.sub_prefix hj)⟩
  have lk : LoopPre t (St + BitVec.ofNat 64 (64+P%16)) O j :=
    ⟨by omega_arith, by rw [tr,tw]; exact covers_left (h.env.perm.stC (by omega_arith)),ls.wr,
      ((hw.take hj).ok.st.sub_right (Lay.stSub (by omega_arith))).symm⟩
  have sg (r : Reg) (h₁ : r ∉ [.x11,.x25,.x9]) (h₂ : r ∉ minRegs) := (reg.others r h₁).trans (g r h₂)
  refine (xorBytes_ok (byte_start ((sg _ (by decide) (by decide)).trans h.x23) x11
    ((sg _ (by decide) (by decide)).trans x26) ((reg.others _ (by decide)).trans x10)
    ((sg _ (by decide) (by decide)).trans h.x24)) ls lk hj).mono fun u a => ?_
  have hmem := a.mem
  rw [tm] at hmem
  have len := length_xorBytes s.mem D (St + BitVec.ofNat 64 (64+P%16)) j
  have fw : Frame [⟨O,j⟩] s.mem u.mem := by rw [hmem]; exact writeBytes_frame' _ len
  have kframe (d : Nat) (hd : d+16 ≤ 80) := blockAt_frame fw (p := St + BitVec.ofNat 64 d) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ((hw.take hj).ok.st.sub_right (Lay.stSub hd)).symm)
  have kept : ∀ r ∈ [Reg.x19,.x20,.x21,.x22,.x27,.x28], u.gpr r = s.gpr r := by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;> exact (a.gpr _ (by decide)).trans (sg _ (by decide) (by decide))
  refine ⟨h.env.keep (fun r hr => kept r (List.mem_append_left [Reg.x22,.x27,.x28] hr)) (a.sp.trans (reg.sp.trans sp))
    (a.rd.trans tr) (a.wr.trans tw), fun r hr => (kept r (List.mem_append_right [Reg.x19,.x20,.x21] hr)).trans (h.kept r hr),
    (kept _ (by decide)).trans h.x22,a.src,a.dst,a.rest,(a.gpr _ (by decide)).trans x25,a.rd.trans tr,a.wr.trans tw,
    (hc.head hoff hspace).congr (kframe 48 (by decide)) (kframe 64 (by decide)),?_,fw⟩
  have read := bytesAt_writeBytes_self s.mem O _ (by rw [len]; omega_arith)
  rw [len] at read
  rw [hmem,read,xorBytes,← Offset.add_add]
  have e := Proof.Gcm.ctr_head hc hoff (d := bytesAt s.mem D j) (by rw [length_bytesAt]; exact hspace)
  rwa [length_bytesAt] at e

end VG.Proof.AesGcm.AArch64.DirectGather.Generic

/-! The accumulated ciphertext and the last authenticated block across descriptors. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather.Generic

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt gathered gatheredLen)
open VG.Proof.Gcm (Ctr xorKs)
open VG.Proof.AesGcm.AArch64.Gather (sb sl)
open VG.Impl.AesGcm.AArch64.DirectGather (hashO)

structure TextArgs where
  Wn : Nat
  Ctx : Addr
  St : Addr
  W : Addr
  SP : Addr
  R : Nat
  icb : Block
  src : Addr
  count : Nat
  dst : Addr

abbrev TextArgs.gl (a : TextArgs) (s : State) (i : Nat) := gatheredLen 64 s.mem a.src i
abbrev TextArgs.total (a : TextArgs) (s : State) := a.gl s a.count
abbrev TextArgs.pt (a : TextArgs) (s : State) (i : Nat) := gathered 64 s.mem a.src i
abbrev TextArgs.ciph (a : TextArgs) (s : State) := ciphOf s.mem a.Ctx a.R
abbrev atOff (p : Addr) (n : Nat) := p + BitVec.ofNat 64 n
abbrev textFrame (a : TextArgs) (O : Addr) (n : Nat) : List Region :=
  [⟨O,n⟩,⟨atOff a.St 16,16⟩,⟨atOff a.St 48,32⟩,⟨atOff a.W hashO,8⟩,⟨atOff a.W 512,a.Wn-512⟩]

structure PiecesPre (a : TextArgs) (s : State) : Prop where
  lay : Lay a.Wn a.Ctx a.St a.W
  env : Env a.Wn a.Ctx a.St a.W a.SP s
  rounds : a.R = 10 ∨ a.R = 12 ∨ a.R = 14
  x22 : s.gpr .x22 = BitVec.ofNat 64 a.R
  x25 : s.gpr .x25 = 0
  x26 : s.gpr .x26 = a.dst
  x27 : s.gpr .x27 = a.src
  x28 : s.gpr .x28 = BitVec.ofNat 64 a.count
  descLt : 16*a.count < 2^64
  desc : DataOk a.Wn a.St a.W s a.src (16*a.count)
  dst : DataW a.Wn a.Ctx a.St a.W s a.dst (a.total s)
  apart : (⟨a.src,16*a.count⟩ : Region).Disjoint ⟨a.dst,a.total s⟩
  source : ∀ i < a.count, DataOk a.Wn a.St a.W s (sb s.mem a.src i) (sl s.mem a.src i)
  sourceApart : ∀ i < a.count, (⟨sb s.mem a.src i,sl s.mem a.src i⟩ : Region).Disjoint ⟨a.dst,a.total s⟩
  ctr : Ctr s.mem (a.St+48) (a.St+64) (a.ciph s) a.icb 0
  hashPtr : s.mem.readW (a.W+352) 64 = a.dst

structure StreamAt (a : TextArgs) (s : State) (plain : List Byte) (n hashed : Nat) (t : State) : Prop where
  env : Env a.Wn a.Ctx a.St a.W a.SP t
  x22 : t.gpr .x22 = BitVec.ofNat 64 a.R
  offset : t.gpr .x25 = BitVec.ofNat 64 (n%16)
  dst : t.gpr .x26 = atOff a.dst n
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  ctr : Ctr t.mem (a.St+48) (a.St+64) (a.ciph s) a.icb n
  out : bytesAt t.mem a.dst n = xorKs (a.ciph s) a.icb 0 plain
  hashBound : 16*hashed ≤ n
  hashPtr : t.mem.readW (a.W+352) 64 = atOff a.dst (16*hashed)
  y : blockAt t.mem (a.St+16) = Spec.Gcm.ghashFrom (Spec.Gcm.ctxH s.mem a.Ctx) (blockAt s.mem (a.St+16))
    (blocksAt t.mem a.dst hashed)
  frame : Frame (textFrame a a.dst n) s.mem t.mem

structure TextAt (a : TextArgs) (s : State) (i h : Nat) (t : State) : Prop
    extends StreamAt a s (a.pt s i) (a.gl s i) h t where
  desc : t.gpr .x27 = atOff a.src (16*i)
  count : t.gpr .x28 = BitVec.ofNat 64 (a.count-i)

theorem TextAt.start {a s} (h : PiecesPre a s) : TextAt a s 0 0 s := by
  exact ⟨⟨h.env,h.x22,h.x25,by change s.gpr .x26 = a.dst + 0; simpa using h.x26,rfl,rfl,h.ctr,
    rfl,Nat.zero_le _,by simpa [atOff] using h.hashPtr,rfl,Frame.refl _ _⟩,
    by simpa [atOff] using h.x27,h.x28⟩

end VG.Proof.AesGcm.AArch64.DirectGather.Generic

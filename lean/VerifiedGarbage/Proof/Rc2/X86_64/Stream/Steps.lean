import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Verified
import VerifiedGarbage.Proof.Rc2.X86_64.Key
import VerifiedGarbage.Impl.Rc2.X86_64.Stream
import VerifiedGarbage.Proof.Rc2.Stream
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

section

section

/-! # Streaming RC2-CBC on x86-64: the byte-copy loop -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64 VG.X86_64.RegUpd VG.WriteBytes VG.Impl.Rc2.X86_64.Stream

/-- The copy routine's registers: none is its index `r10` or byte `r11`. -/
structure CopyRegs (src dst cnt : Reg) : Prop where
  src10 : src ≠ .r10
  src11 : src ≠ .r11
  dst10 : dst ≠ .r10
  dst11 : dst ≠ .r11
  cnt10 : cnt ≠ .r10
  cnt11 : cnt ≠ .r11

theorem ea_at10 (s : State) (b : Reg) (d i : Nat) (hi : s.gpr .r10 = BitVec.ofNat 64 i) :
    s.ea (at10 b d) = s.gpr b + BitVec.ofNat 64 d + BitVec.ofNat 64 i := by
  simp only [State.ea, at10, hi, BitVec.mul_one, Int.ofNat_eq_natCast, BitVec.ofInt_natCast]
  rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 i)]

theorem copyStep_ok (s : State) {src dst cnt : Reg} (hr : CopyRegs src dst cnt) {S D : Addr} {sd dd i n : Nat}
    (hs : s.gpr src + BitVec.ofNat 64 sd = S) (hd : s.gpr dst + BitVec.ofNat 64 dd = D)
    (hi : s.gpr .r10 = BitVec.ofNat 64 i) (hn : s.gpr cnt = BitVec.ofNat 64 n)
    (r : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (D + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa (copyBody src sd dst dd cnt) s = some s' ∧
      s'.mem = s.mem.writeW (D + BitVec.ofNat 64 i) (s.mem (S + BitVec.ofNat 64 i)) ∧
      s'.gpr .r10 = BitVec.ofNat 64 i + 1 ∧
      s'.zf = some (BitVec.ofNat 64 i + 1 - BitVec.ofNat 64 n == 0) ∧
      (∀ r, r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea₁ : s.ea (at10 src sd) = S + BitVec.ofNat 64 i := by rw [ea_at10 s src sd i hi, hs]
  have ea₂ : (s.setReg .r11 ((s.mem (S + BitVec.ofNat 64 i)).setWidth 64)).ea (at10 dst dd) =
      D + BitVec.ofNat 64 i := by
    rw [ea_at10 _ dst dd i (by rw [gpr_setReg_of_ne _ _ (by decide)]; exact hi), gpr_setReg_of_ne _ _ hr.dst11, hd]
  have n₁ : (s.setReg .r11 ((s.mem (S + BitVec.ofNat 64 i)).setWidth 64)).gpr cnt = BitVec.ofNat 64 n := by
    rw [gpr_setReg_of_ne _ _ hr.cnt11, hn]
  refine ⟨_, by
    simp only [↓reduceIte, Nat.reducePow, BitVec.reduceSignExtend, copyBody, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, State.load8, State.store8, Option.bind_some, Option.map_some, ea₁, ea₂, r, w, 
      wr_setReg, rd_setReg, mem_setReg]
    rfl, ?_⟩
  have h10 : (s.setReg .r11 ((s.mem (S + BitVec.ofNat 64 i)).setWidth 64)).gpr .r10 = BitVec.ofNat 64 i := by
    rw [gpr_setReg_of_ne _ _ (by decide), hi]
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp only [mem_arithFlags, mem_setReg, gpr_setReg_self,
      BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide), BitVec.setWidth_eq]
  · simp only [gpr_arithFlags, gpr_setReg_self, h10]; rfl
  · simp only [zf_arithFlags, gpr_setReg_self, h10, gpr_setReg_of_ne _ _ hr.cnt10, gpr_arithFlags, n₁]; rfl
  · intro r' h₁ h₂
    simp only [gpr_arithFlags, gpr_setReg_of_ne _ _ h₁, gpr_setReg_of_ne _ _ h₂]

theorem beq_zero {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x == 0) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro he
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this
    simpa using this
  · intro he; rw [he]; rfl

theorem guard_ok (s : State) {cnt : Reg} (hc : cnt ≠ .r10) {n : Nat} (hn : s.gpr cnt = BitVec.ofNat 64 n)
    (hn' : n < 2 ^ 64) :
    ∃ s', runBlock isa [.mov32 .r10 (.imm 0), .alu .test cnt (.reg cnt)] s = some s' ∧
      s'.gpr .r10 = BitVec.ofNat 64 0 ∧ s'.zf = some (decide (n = 0)) ∧
      (∀ r, r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu, State.setReg32,
      Option.map_some, Option.bind_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp only [gpr_arithFlags, gpr_setReg_self]; rfl
  · simp only [zf_arithFlags, gpr_setReg_of_ne _ _ hc, hn, BitVec.and_self, beq_zero hn']
  · intro r h; simp only [gpr_arithFlags, gpr_setReg_of_ne _ _ h]

theorem succ_ofNat (i : Nat) : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := (BitVec.ofNat_add i 1).symm

/-- The copy routine: `n` bytes from `S = src + sd` to `D = dst + dd`, for
separate ranges. -/
theorem copy_ok (s : State) {src dst cnt : Reg} (hr : CopyRegs src dst cnt) {S D : Addr} {sd dd n : Nat}
    (hs : s.gpr src + BitVec.ofNat 64 sd = S) (hd : s.gpr dst + BitVec.ofNat 64 dd = D)
    (hn : s.gpr cnt = BitVec.ofNat 64 n) (hn' : n < 2 ^ 64)
    (rd : ∀ i < n, InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) 1)
    (wr : ∀ i < n, InRegions s.wr (D + BitVec.ofNat 64 i) 1)
    (sep : (Region.mk S n).Disjoint ⟨D, n⟩) :
    WP isa (copy src sd dst dd cnt) s fun s' => s'.mem = writeBytes s.mem D (Spec.Rc2.bytesAt s.mem S n) ∧
      (∀ r, r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, r10₁, zf₁, g₁, mem₁, rd₁, wr₁⟩ := guard_ok s hr.cnt10 hn hn'
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (by simpa [eval] using zf₁) (fun h0 => ?_) (fun h0 => ?_)
  · have h0 : n = 0 := of_decide_eq_true h0
    subst h0
    exact WP.block_nil ⟨by rw [mem₁]; simp [Spec.Rc2.bytesAt, writeBytes_nil],
      fun r h₁ _ => g₁ r h₁, rd₁, wr₁⟩
  have hn₀ : 0 < n := Nat.pos_of_ne_zero (of_decide_eq_false h0)
  refine WP.loop (M := isa) (body := .block (copyBody src sd dst dd cnt)) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r10 = BitVec.ofNat 64 i ∧
      t.mem = writeBytes s.mem D (Spec.Rc2.bytesAt s.mem S i) ∧
      (∀ r, r ≠ .r10 → r ≠ .r11 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, hn₀, r10₁, by rw [mem₁]; simp [Spec.Rc2.bytesAt, writeBytes_nil],
      fun r h₁ _ => g₁ r h₁, rd₁, wr₁⟩
  rintro k t ⟨i, rfl, hi, r10, mem, g, trd, twr⟩
  obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := copyStep_ok t hr
    (by rw [g _ hr.src10 hr.src11, hs]) (by rw [g _ hr.dst10 hr.dst11, hd]) r10
    (by rw [g _ hr.cnt10 hr.cnt11, hn]) (by rw [trd, twr]; exact rd i hi) (by rw [twr]; exact wr i hi)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (Spec.Rc2.bytesAt s.mem S i).length = i := bytesAt_length _ _ _
  have hx : writeBytes s.mem D (Spec.Rc2.bytesAt s.mem S i) (S + BitVec.ofNat 64 i) = s.mem (S + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem D _ (R := ⟨D, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sep _ (Offset.contains_base S (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  have hmem : t'.mem = writeBytes s.mem D (Spec.Rc2.bytesAt s.mem S (i + 1)) := by
    rw [mem', mem, hx, bytesAt_succ, writeBytes_snoc s.mem D (Spec.Rc2.bytesAt s.mem S i)
      (s.mem (S + BitVec.ofNat 64 i)) (by rw [hlen]; omega), hlen]
  have hz : t'.zf = some (decide (i + 1 = n)) := by
    rw [zf', succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  have gg : ∀ r, r ≠ .r10 → r ≠ .r11 → t'.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g' r h₁ h₂, g r h₁ h₂]
  by_cases he : i + 1 = n
  · left
    refine ⟨by simp [eval, hz, he], by rw [hmem, he], gg, by rw [rd', trd], by rw [wr', twr]⟩
  · right
    refine ⟨by simp [eval, hz, he], n - (i + 1), by omega, i + 1, rfl, by omega, by rw [r10', succ_ofNat], hmem, gg,
      by rw [rd', trd], by rw [wr', twr]⟩

end VG.Proof.Rc2.X86_64.Stream

end

/-! # Streaming RC2-CBC on x86-64: the function-level contracts -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64

/-- `vg_rc2_cbc_init(key = rdi, key_len = rsi, effective_bits = rdx, iv = rcx,
iv_len = r8, ctx = r9, scratch = [rsp + 8])`, which calls key expansion. -/
def initContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let iv : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let ctx : Region := ⟨s.gpr .r9, 144⟩
    let buf : Region := ⟨stackArg s 0, 576⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 8
    8 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 16 ≤ 2 ^ 64 ∧
      s.rd = [key, iv, args] ∧ s.wr = [ctx, buf] ∧
      key.Disjoint ctx ∧ key.Disjoint buf ∧ iv.Disjoint ctx ∧ iv.Disjoint buf ∧ ctx.Disjoint buf ∧
      ctx.Disjoint args ∧ buf.Disjoint args ∧
      ret.Disjoint key ∧ ret.Disjoint iv ∧ ret.Disjoint ctx ∧ ret.Disjoint buf ∧ ret.Disjoint args ∧
      stack.Disjoint key ∧ stack.Disjoint iv ∧ stack.Disjoint ctx ∧ stack.Disjoint buf ∧ stack.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r9).toNat + 144 ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + 576 ≤ 2 ^ 64
  post s s' :=
    ∀ direction, match Spec.Rc2.initWithEffectiveBits (Spec.Rc2.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
        (Spec.Rc2.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) direction (s.gpr .rdx).toNat with
      | .ok c => (s'.gpr .rax).setWidth 32 = 0 ∧ Spec.Rc2.contextAt s'.mem (s.gpr .r9) direction 0 = c
      | .error e => ((s'.gpr .rax).setWidth 32).toNat = e.code
  pub s₁ s₂ := PublicRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] s₁ s₂ ∧ stackArg s₁ 0 = stackArg s₂ 0

/-- The update functions (`ctx = rdi, pending_len = rsi, data = rdx,
len = rcx, out = r8, out_len = r9, scratch = [rsp + 8]`), which call CBC. -/
def updateContract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .rdi, 144⟩
    let data : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let out : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let buf : Region := ⟨stackArg s 0, 576⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 16
    16 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 16 ≤ 2 ^ 64 ∧
      s.rd = [data, args] ∧ s.wr = [ctx, out, buf] ∧
      ctx.Disjoint data ∧ ctx.Disjoint out ∧ ctx.Disjoint buf ∧ ctx.Disjoint args ∧
      data.Disjoint out ∧ data.Disjoint buf ∧ out.Disjoint buf ∧ out.Disjoint args ∧ buf.Disjoint args ∧
      ret.Disjoint ctx ∧ ret.Disjoint data ∧ ret.Disjoint out ∧ ret.Disjoint buf ∧ ret.Disjoint args ∧
      stack.Disjoint ctx ∧ stack.Disjoint data ∧ stack.Disjoint out ∧ stack.Disjoint buf ∧ stack.Disjoint args ∧
      (s.gpr .rdi).toNat + 144 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + 576 ≤ 2 ^ 64 ∧
      (s.gpr .rsi).toNat < 8 ∧ (s.gpr .r9).toNat = ((s.gpr .rsi).toNat + (s.gpr .rcx).toNat) / 8 * 8
  post s s' :=
    let result := Spec.Rc2.update (Spec.Rc2.contextAt s.mem (s.gpr .rdi) d (s.gpr .rsi).toNat)
      (Spec.Rc2.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    Spec.Rc2.contextAt s'.mem (s.gpr .rdi) d (((s.gpr .rsi).toNat + (s.gpr .rcx).toNat) % 8) = result.1 ∧
      Spec.Rc2.bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat = result.2
  pub s₁ s₂ := PublicRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] s₁ s₂ ∧ stackArg s₁ 0 = stackArg s₂ 0

def updateSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rdx => 0x2000 | .r8 => 0x3000 | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6009 then 0x40 else 0
  rd := [⟨0x2000, 0⟩, ⟨0x6008, 8⟩]
  wr := [⟨0x1000, 144⟩, ⟨0x3000, 0⟩, ⟨0x4000, 576⟩]

def initSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rcx => 0x2000 | .r9 => 0x3000 | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6009 then 0x40 else 0
  rd := [⟨0x1000, 0⟩, ⟨0x2000, 0⟩, ⟨0x6008, 8⟩]
  wr := [⟨0x3000, 144⟩, ⟨0x4000, 576⟩]

theorem publicRegs_seven (s₁ s₂ : State) : PublicRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] s₁ s₂ ↔
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp := by
  simp [PublicRegs]

theorem stackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

theorem args_getD (s : State) : (s.gpr .rdi :: s.gpr .rsi :: s.gpr .rdx :: s.gpr .rcx :: s.gpr .r8 :: s.gpr .r9 ::
    List.map (stackArg s) (List.range 1)).getD 6 0 = stackArg s 0 := rfl

theorem update_implies (d : Spec.Rc2.Direction) : (updateContract d).Implies (Spec.Rc2.cbcUpdateContract abi d 16) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, abi, argRegs, updateContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq] at h
    sig_pre [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, abi, argRegs, updateContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, abi, argRegs, updateContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
  post := by sig_implies_post [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, abi, argRegs, updateContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, abi, argRegs, updateContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    sig_split h
    rename_i h1 h2 h3 h4 h5 h6 h7
    exact ⟨(publicRegs_seven _ _).2 ⟨h2, h3, h4, h5, h6, h7, h1⟩, h⟩
  sat := by sig_implies_sat [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, abi, argRegs, updateContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq] [updateSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using updateSatState

theorem init_implies : initContract.Implies (Spec.Rc2.cbcInitContract abi 8) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, abi, argRegs, initContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq] at h
    sig_pre [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, abi, argRegs, initContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, abi, argRegs, initContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
  post := by sig_implies_post [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, abi, argRegs, initContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, abi, argRegs, initContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    sig_split h
    rename_i h1 h2 h3 h4 h5 h6 h7
    exact ⟨(publicRegs_seven _ _).2 ⟨h2, h3, h4, h5, h6, h7, h1⟩, h⟩
  sat := by sig_implies_sat [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, abi, argRegs, initContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq] [initSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using initSatState

end VG.Proof.Rc2.X86_64.Stream

end

/-! # Streaming RC2-CBC on x86-64: the straight-line blocks -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64 VG.Impl.Rc2.X86_64.Stream

theorem toNat_eq (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by simp

/-- `test r, r`: ZF is set iff `r` is 0. -/
theorem test_ok (s : State) (r : Reg) {n : Nat} (hn : s.gpr r = BitVec.ofNat 64 n) (hn' : n < 2 ^ 64) :
    ∃ s', runBlock isa [.alu .test r (.reg r)] s = some s' ∧ s'.zf = some (decide (n = 0)) ∧ Keep [] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]
    rfl, ?_⟩
  refine ⟨?_, ⟨fun r _ => by rw [gpr_arithFlags], rfl, rfl, rfl⟩⟩
  rw [zf_arithFlags, hn, BitVec.and_self, beq_zero hn']

theorem shortArgs_ok (s : State) :
    ∃ s', runBlock isa [rr .rax .rdi, .alu .add .rax (.reg .rsi)] s = some s' ∧
      s'.gpr .rax = s.gpr .rdi + s.gpr .rsi ∧ Keep [.rax] s s' := by
  refine ⟨_, by
    simp only [reduceCtorEq, Nat.reducePow, not_false_eq_true, rr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, Option.bind_some, Option.map_some, gpr_setReg_self, gpr_setReg_of_ne]
    rfl, ?_⟩
  refine ⟨by rw [gpr_setReg_self], fun r hr => ?_, rfl, rfl, rfl⟩
  have hr : r ≠ .rax := by simpa using hr
  rw [gpr_setReg_of_ne _ _ hr, gpr_arithFlags, gpr_setReg_of_ne _ _ hr]

theorem toOut_ok (s : State) :
    ∃ s', runBlock isa toOut s = some s' ∧
      s'.gpr .r9 = s.gpr .r9 - s.gpr .rsi ∧ s'.gpr .r8 = s.gpr .r8 + s.gpr .rsi ∧ Keep [.r9, .r8] s s' := by
  refine ⟨_, by
    simp only [reduceCtorEq, Nat.reducePow, not_false_eq_true, toOut, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, Option.bind_some, gpr_setReg_of_ne, gpr_arithFlags]
    rfl, ?_⟩
  refine ⟨?_, by rw [gpr_setReg_self], fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [gpr_setReg_of_ne _ _ (by decide), gpr_arithFlags, gpr_setReg_self]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg_of_ne _ _ hr.2, gpr_arithFlags, gpr_setReg_of_ne _ _ hr.1]

theorem toPending_ok (s : State) :
    ∃ s', runBlock isa toPending s = some s' ∧
      s'.gpr .rdx = s.gpr .rdx + s.gpr .r9 ∧ s'.gpr .rcx = s.gpr .rcx - s.gpr .r9 ∧ Keep [.rdx, .rcx] s s' := by
  refine ⟨_, by
    simp only [reduceCtorEq, Nat.reducePow, not_false_eq_true, toPending, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, Option.bind_some, gpr_setReg_of_ne, gpr_arithFlags]
    rfl, ?_⟩
  refine ⟨?_, by rw [gpr_setReg_self], fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [gpr_setReg_of_ne _ _ (by decide), gpr_arithFlags, gpr_setReg_self]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg_of_ne _ _ hr.2, gpr_arithFlags, gpr_setReg_of_ne _ _ hr.1]

theorem cbcArgs_ok (s : State) (h : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa cbcArgs s = some s' ∧
      s'.gpr .rdi = s.gpr .rdi ∧ s'.gpr .rsi = s.gpr .rdi + 128 ∧ s'.gpr .rdx = s.gpr .r8 - s.gpr .rsi ∧
      s'.gpr .rcx = (s.gpr .r9 + s.gpr .rsi) >>> 3 ∧
      s'.gpr .r8 = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 8) 64 ∧
      Keep [.r8, .r9, .rdx, .rcx, .rsi] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [cbcArgs, rr, memOp, runBlock_cons, runStep_some, runBlock_nil,
      exec, readSrc, execAlu, execShift, State.load64, State.ea, offset_nat, Option.bind_some, Option.map_some,
      gpr_setReg_self, gpr_setReg_of_ne, gpr_arithFlags, gpr_setFlags, rd_setReg, wr_setReg, rd_arithFlags,
      wr_arithFlags, rd_setFlags, wr_setFlags, mem_setReg, mem_arithFlags, mem_setFlags, h, ite_true]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals try simp (config := {decide := true}) only [gpr_setReg_self, gpr_setReg_of_ne, gpr_arithFlags,
    gpr_setFlags, reduceCtorEq, not_false_eq_true]
  · rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hr
    simp only [gpr_setReg_of_ne _ _ h₁, gpr_setReg_of_ne _ _ h₂, gpr_setReg_of_ne _ _ h₃,
      gpr_setReg_of_ne _ _ h₄, gpr_setReg_of_ne _ _ h₅, gpr_arithFlags, gpr_setFlags]

end VG.Proof.Rc2.X86_64.Stream

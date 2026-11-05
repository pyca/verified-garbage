module

public import VerifiedGarbage.Proof.AesCbc.Rounds
public import VerifiedGarbage.Impl.AesCbc.X86_64.VaesDecrypt
public import VerifiedGarbage.Proof.AesCbc.X86_64.Decrypt
import VerifiedGarbage.Proof.Aes.X86_64.VaesBlocks.Blocks
import VerifiedGarbage.Proof.Aes.X86_64.VaesBlocks.Dec
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Impl.AesCbc.X86_64.VaesDecrypt
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.Taint

-- separate module: the VAES loop's verification is independent of the AES-NI caller's.
/-! # CBC decryption with two independent states in each VAES register -/

@[expose] public section
namespace VG.Proof.AesCbc.X86_64.VaesDecrypt
open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Proof.Aes.X86_64.AesNi
open VG.Proof.AesCbc.X86_64.Decrypt (DataInv chaining output)
open VG.Impl.Aes.X86_64.AesNi (at_ regs8 imcKeys blocksLoad)
open VG.Impl.AesCbc.X86_64.VaesDecrypt
open VG.Spec.Aes (bytesAt)

theorem extract_ok (b : XReg) (s : State) :
    WP isa (.block [.vop (.vextracti128 .xmm14 b 1)]) s fun t =>
      t.xmm .xmm14 = s.lane b 1 ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ .xmm14 → ∀ l, t.lane r l = s.lane r l) := by
  rw [WP.block_cons_iff]
  refine ⟨_,rfl,WP.block_nil ?_⟩
  simp only [reduceVOpExec,show (1 : BitVec 8).getLsbD 0 = true from rfl,ite_true]
  refine ⟨by simp only [xmm_setV,ite_true],rfl,rfl,rfl,rfl,fun r hr l => ?_⟩
  simp only [State.lane_setV128,ite_eq_right hr]

theorem finishData_ok {m₀ : Mem} {D : Addr} {n c : Nat} {F : Nat → Spec.Aes.State}
    {chain : Nat → BitVec 128} (hn : 16*n ≤ 2^64)
    (hnext : ∀ k < n, chain (k+1) = m₀.readW (D + BitVec.ofNat 64 (16*k)) 128) :
    ∀ (rs : List XReg) (j : Nat) (s : State), rs.Nodup → .xmm14 ∉ rs → .xmm15 ∉ rs →
    s.gpr .rdx = D + BitVec.ofNat 64 (16*c) → c+2*j+2*rs.length ≤ n →
    (⟨D,16*n⟩ : Region) ∈ s.wr → DataInv m₀ s.mem D n (c+2*j) F →
    s.xmm .xmm15 = chain (c+2*j) →
    (∀ k (h : k < rs.length), ∀ l < 2,
      st (s.lane rs[k] l ^^^ chain (c+2*(j+k)+l)) = F (c+2*(j+k)+l)) →
    WP isa (.block (finishData rs j)) s fun t =>
      DataInv m₀ t.mem D n (c+2*j+2*rs.length) F ∧
      t.xmm .xmm15 = chain (c+2*j+2*rs.length) ∧ Frame [⟨D,16*n⟩] s.mem t.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ .xmm15 → r ≠ .xmm14 → r ∉ rs → ∀ l < 2, t.lane r l = s.lane r l)
  | [], _, s, _, _, _, _, _, _, hd, hx, _ =>
    WP.block_nil ⟨by simpa using hd,by simpa using hx,Frame.refl _ _,rfl,rfl,rfl,fun _ _ _ _ _ _ => rfl⟩
  | b::bs, j, s, hnd, h14, h15, hg, hc, hw, hd, hx, hv => by
    have hb14 : b ≠ .xmm14 := fun h => h14 (h ▸ List.mem_cons_self)
    have hb15 : b ≠ .xmm15 := fun h => h15 (h ▸ List.mem_cons_self)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have h14' : .xmm14 ∉ bs := fun h => h14 (List.mem_cons_of_mem _ h)
    have h15' : .xmm15 ∉ bs := fun h => h15 (List.mem_cons_of_mem _ h)
    rw [finishData,WP.block_append_iff,WP.block_append_iff]
    refine WP.mono (extract_ok b s) fun u ⟨hu,gu,mu,ru,wu,ou⟩ => ?_
    refine WP.mono (Decrypt.finishData_ok (m₀ := m₀) (D := D) (n := n) (c := c) (F := F) (chain := chain)
      hn hnext [b,.xmm14] (2*j) u (by simp [hb14]) (by
        intro h
        simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with h | h
        · exact hb15 h.symm
        · cases h)
      (by rw [gu]; exact hg) (by simp only [List.length_cons,List.length_nil]; simp only [List.length_cons] at hc; omega_arith) (wu ▸ hw) (by rw [mu]; exact hd)
      (by rw [← show u.lane .xmm15 0 = u.xmm .xmm15 from rfl,ou _ (by decide),State.lane]; exact hx)
      (fun k hk => by
        have hh : k < 2 := hk
        rcases (show k=0 ∨ k=1 by omega_arith) with rfl | rfl
        · have hv0 : st (s.lane b 0 ^^^ chain (c+2*j)) = F (c+2*j) := hv 0 (by simp) 0 (by decide)
          change st (u.xmm b ^^^ chain (c+2*j)) = F (c+2*j)
          rw [← show u.lane b 0 = u.xmm b from rfl,ou b hb14 0]
          exact hv0
        · have hv1 : st (s.lane b 1 ^^^ chain (c+2*j+1)) = F (c+2*j+1) := hv 0 (by simp) 1 (by decide)
          change st (u.xmm .xmm14 ^^^ chain (c+2*j+1)) = F (c+2*j+1)
          rw [hu]
          exact hv1))
      fun v ⟨hdv,hxv,hfv,gv,rv,wv,yv,ov⟩ => ?_
    have keep (r : XReg) (h₁ : r ≠ .xmm15) (h₂ : r ≠ .xmm14) (h₃ : r ≠ b) (l : Nat) :
        v.lane r l = s.lane r l := by
      by_cases hl : l=0
      · subst hl
        change v.xmm r = s.xmm r
        rw [ov r h₁ (by simp [h₂,h₃])]
        exact ou r h₂ 0
      · simp only [State.lane,ite_eq_right hl]
        rw [yv]
        simpa only [State.lane,ite_eq_right hl] using ou r h₂ l
    refine WP.mono (finishData_ok (m₀ := m₀) (D := D) (n := n) (c := c) (F := F) (chain := chain)
      hn hnext bs (j+1) v (List.nodup_cons.mp hnd).2 h14' h15'
      (by rw [gv,gu]; exact hg) (by simp only [List.length_cons] at hc; omega_arith) (by rw [wv,wu]; exact hw)
      (by simpa [Nat.mul_add,Nat.add_assoc] using hdv) (by simpa [Nat.mul_add,Nat.add_assoc] using hxv)
      (fun k hk l hl => by
        rw [keep _ (fun h => h15' (h ▸ List.getElem_mem hk)) (fun h => h14' (h ▸ List.getElem_mem hk))
          (fun h => hbs (h ▸ List.getElem_mem hk)) l]
        have he := hv (k+1) (by simp; omega_arith) l hl
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using he))
      fun t ⟨hdt,hxt,hft,gt,rt,wt,ot⟩ => ?_
    have he : c+2*(j+1)+2*bs.length = c+2*j+2*(b::bs).length := by simp; omega_arith
    rw [he] at hdt hxt
    rw [mu] at hfv
    exact ⟨hdt,hxt,hfv.trans hft,gt.trans (gv.trans gu),rt.trans (rv.trans ru),wt.trans (wv.trans wu),
      fun r h₁ h₂ h₃ l hl => (ot r h₁ h₂ (fun h => h₃ (List.mem_cons_of_mem _ h)) l hl).trans
        (keep r h₁ h₂ (fun h => h₃ (h ▸ List.mem_cons_self)) l)⟩

theorem group16_ok {s₀ s : State} (hp : UPre s₀) {c : Nat} (hc : c+16 ≤ N s₀)
    (hI : Decrypt.Inv s₀ c c s) (after : List Instr) {Q : State → Prop}
    (hQ : ∀ t, Decrypt.Inv s₀ (c+16) c t → WP isa (.block after) t Q) :
    WP isa (.seq (.block (Impl.Aes.X86_64.VaesBlocks.loadData regs8 0))
      (.seq (Impl.Aes.X86_64.VaesBlocks.aesDec regs8) (.block (finishData regs8 0 ++ after)))) s Q := by
  have hnd : regs8.Nodup := by decide
  have hw := hp.data_wrap
  have addr (k l : Nat) :
      s.gpr .rdx + BitVec.ofNat 64 (16*(2*(0+k)+l)) = blk s₀ (c+2*k+l) := by
    rw [hI.rdx,blk,blk,Offset.add_add_eq _ (c := 16*(c+2*k+l)) (by omega_arith)]
  refine WP.seq (WP.mono (Proof.Aes.X86_64.VaesBlocks.loadData_ok regs8 0 s hnd (fun k hk => by
    have hk' : k < 8 := hk
    rw [ofInt_natCast,hI.rdx,blk,Offset.add_add_eq _ (c := 16*c+32*(0+k)) (by omega_arith),hI.rd,hI.wr,hp.rd,hp.wr]
    exact ⟨dataR s₀,by simp,Offset.contains_base _ (by omega_arith) (by omega_arith)⟩))
    fun u ⟨hl,gl,ml,rl,wl,xl⟩ => ?_)
  have hku : DKeys (R s₀) (wK s₀) u :=
    Ecb.dkeys_congr hI.keys (by rw [gl]) (by rw [gl]) rl wl (by rw [ml]) (fun _ _ _ => by rw [ml])
  refine WP.seq (WP.mono (Proof.Aes.X86_64.VaesBlocks.aesDec_ok regs8 hnd (by decide) hp.rounds u hku
    (by rw [gl,hI.rsi]; simp) (by rw [gl,hI.r10,hI.rdi])) fun v ⟨ha,fa⟩ => ?_)
  have gv : v.gpr = s.gpr := fa.gpr.trans gl
  have mv : v.mem = s.mem := fa.mem.trans ml
  have hx : v.xmm .xmm15 = chaining s₀ c := by
    rw [← show v.lane .xmm15 0 = v.xmm .xmm15 from rfl,fa.lane _ (by decide) 0 (by decide),
      xl _ (by decide) 0 (by decide)]
    exact hI.chain
  rw [WP.block_append_iff]
  refine WP.mono (finishData_ok (m₀ := s₀.mem) (D := Dp s₀) (n := N s₀) (c := c)
    (F := output s₀) (chain := chaining s₀) (by omega_arith) (fun _ _ => rfl) regs8 0 v hnd
    (by decide) (by decide) (by rw [gv,hI.rdx]) (by change c+16 ≤ N s₀; exact hc)
    (by rw [fa.wr,wl,hI.wr,hp.wr]; simp) (by simpa [mv] using hI.data) (by simpa using hx)
    (fun k hk l hll => by
      have hk' : k < 8 := hk
      have he := ha _ (List.getElem_mem hk) l hll
      rw [hl k hk l hll,addr k l,hI.data _ (by omega_arith),ite_eq_right (by omega_arith)] at he
      apply st_ext
      intro i hi
      rw [getD_st _ hi,byte_xor,← getD_st _ hi,he]
      change _ = (Vector.ofFn fun i =>
        (Spec.Aes.invCipher (R s₀) (wK s₀) (Spec.Aes.stateAt s₀.mem (blk s₀ (c+2*(0+k)+l)))).getD i.1 0 ^^^
          byte (chaining s₀ (c+2*(0+k)+l)) i.1).getD i 0
      rw [getD_ofFn hi]; simp only [Nat.zero_add])) fun t ⟨hd,hchain,hf,hg,hr,hw,_⟩ => ?_
  have gt : t.gpr = s.gpr := hg.trans gv
  have rt : t.rd = s.rd := hr.trans (fa.rd.trans rl)
  have wt : t.wr = s.wr := hw.trans (fa.wr.trans wl)
  rw [mv] at hf
  refine hQ t ⟨hc,Decrypt.keys_stable hp hI.keys hI.rdi hI.r8 gt rt wt hf,
    by rw [gt]; exact hI.rdi,by rw [gt]; exact hI.rsi,by rw [gt]; exact hI.r8,
    by rw [gt]; exact hI.r10,by rw [gt]; exact hI.r11,by rw [gt]; exact hI.rdx,
    by rw [gt]; exact hI.rcx,by exact hchain,by exact hd,
    hI.frame.trans (hf.mono (by simp)),rt.trans hI.rd,wt.trans hI.wr⟩

/-- The sixteen-block body. -/
theorem body16_ok {s₀ : State} (hp : UPre s₀) {c : Nat} (hc : c + 16 ≤ N s₀) {s : State} (hI : Decrypt.Inv s₀ c c s) :
    WP isa blocks16 s fun s' => Decrypt.Inv s₀ (c + 16) (c + 16) s' ∧
      s'.cf = some (decide (N s₀ - (c + 16) < 16)) := by
  have hn : 16*N s₀ ≤ 2^64 := by have := hp.data_wrap; omega_arith
  refine group16_ok hp hc hI _ fun s₁ hI₁ => ?_
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have hrdx := hI₁.rdx
  have hrcx := hI₁.rcx
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e256, e16, hrdx, hrcx,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have hsub : BitVec.ofNat 64 (N s₀ - c) - 16 = BitVec.ofNat 64 (N s₀ - (c + 16)) := by
    have := (s₀.gpr .rcx).isLt; bv_omega
  refine ⟨{ hI₁ with
    keys := Ecb.dkeys_congr hI₁.keys (by simp) (by simp) rfl rfl rfl (fun _ _ _ => rfl)
    rdi := by simp [hI₁.rdi]
    rsi := by simp [hI₁.rsi]
    r8 := by simp [hI₁.r8]
    r11 := by simp [hI₁.r11]
    r10 := by simp [hI₁.r10]
    rdx := by simp only [reduceCtorEq, ↓reduceIte, blk]; bv_omega
    rcx := by simp only [ite_true, reduceCtorEq, ite_false]; exact hsub }, ?_⟩
  simp only [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show N s₀ - (c + 16) < 2 ^ 64 by omega_arith),
    show (16 : BitVec 64).toNat = 16 from rfl]


theorem compare16_ok {s₀ s : State} {c : Nat} (hI : Decrypt.Inv s₀ c c s) :
    WP isa (.block [.alu .cmp .rcx (.imm 16)]) s fun t =>
      Decrypt.Inv s₀ c c t ∧ t.cf = some (decide (N s₀-c < 16)) := by
  apply WP.of_runBlock
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,arithFlags,
    State.setFlags,isa,e16,Option.bind_some,Option.some.injEq,exists_eq_left']
  refine ⟨{ hI with keys := hI.keys.of_frame (rs := []) ⟨rfl,rfl,rfl,rfl,fun _ _ => rfl⟩ },?_⟩
  rw [hI.rcx,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have hn : N s₀ < 2^64 := (s₀.gpr .r8).isLt; omega_arith)]
  rfl

theorem wide_ok {s₀ : State} (hp : UPre s₀) {c₀ : Nat} {s : State} (hI : Decrypt.Inv s₀ c₀ c₀ s)
    (hcf : s.cf = some (decide (N s₀-c₀ < 16))) :
    WP isa (.ite .b (.block []) (.loop blocks16 .ae)) s fun t =>
      ∃ c, N s₀-c < 16 ∧ Decrypt.Inv s₀ c c t := by
  refine WP.ite (decide (N s₀-c₀ < 16)) (by simp [eval,hcf]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil ⟨c₀,by simpa using h,hI⟩
  · let I16 : Nat → State → Prop := fun m t =>
      ∃ c, m=N s₀-c ∧ c+16 ≤ N s₀ ∧ Decrypt.Inv s₀ c c t
    have hs : ∀ m t, I16 m t → WP isa blocks16 t fun t' =>
        (eval .ae t'=some false ∧ ∃ c, N s₀-c < 16 ∧ Decrypt.Inv s₀ c c t') ∨
        (eval .ae t'=some true ∧ ∃ m' < m, I16 m' t') := by
      rintro m t ⟨c,rfl,hc,hi⟩
      refine WP.mono (body16_ok hp hc hi) fun t' ⟨hi',hcf'⟩ => ?_
      by_cases hh : N s₀-(c+16) < 16
      · exact .inl ⟨by simp [eval,hcf',hh],c+16,hh,hi'⟩
      · exact .inr ⟨by simp [eval,hcf',hh],N s₀-(c+16),by omega_arith,c+16,rfl,by omega_arith,hi'⟩
    exact WP.loop (M := isa) I16 hs (N s₀-c₀) s ⟨c₀,rfl,by simp at h; omega_arith,hI⟩

theorem exit_ok {s₀ s : State} {c : Nat} (hI : Decrypt.Inv s₀ c c s) :
    WP isa (.block [.vop .vzeroupper,.alu .cmp .rcx (.imm 8)]) s fun t =>
      Decrypt.Inv s₀ c c t ∧ t.cf = some (decide (N s₀-c < 8)) := by
  apply WP.of_runBlock
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,readSrc,reduceVOpExec,
    arithFlags,State.setFlags,isa,e8,Option.bind_some,Option.some.injEq,exists_eq_left']
  refine ⟨{ hI with keys := hI.keys.of_frame (rs := []) ⟨rfl,rfl,rfl,rfl,fun _ _ => rfl⟩ },?_⟩
  rw [hI.rcx,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have hn : N s₀ < 2^64 := (s₀.gpr .r8).isLt; omega_arith)]
  rfl

theorem correct_wp {s₀ : State} (hp : UPre s₀) : WP isa decrypt s₀ fun t =>
    (cbcX86_64 false).post s₀ t ∧ Frame [ivR s₀,dataR s₀,⟨S s₀,224⟩] s₀.mem t.mem := by
  refine WP.seq (WP.mono (Decrypt.setup_ok hp) fun s ⟨hI,_⟩ => ?_)
  refine WP.seq (WP.mono (compare16_ok hI) fun u ⟨hIu,hcf⟩ => ?_)
  refine WP.seq (WP.mono (wide_ok hp hIu hcf) fun v ⟨c,_,hIv⟩ => ?_)
  refine WP.seq (WP.mono (exit_ok hIv) fun w ⟨hIw,hcfw⟩ => ?_)
  exact WP.seq (WP.mono (Decrypt.tail_ok hp hIw hcfw) fun t hi => Decrypt.finish_wp hp hi)

theorem keeps (r : Reg) (hr : r ∈ calleeSaved) : ∀ i ∈ instrs decrypt, Taint.clobbers i r = false := by
  have h : decrypt.allInstrs (fun i => calleeSaved.all fun r => !Taint.clobbers i r) = true := by
    decide +kernel
  rw [Code.allInstrs_eq,List.all_eq_true] at h
  intro i hi
  simpa using List.all_eq_true.mp (h i hi) r hr

theorem correct (s : State) (hs : (cbcX86_64 false).pre s) :
    ∃ tr t, Exec isa decrypt s tr t ∧ abiPreserved s t ∧ (cbcX86_64 false).post s t := by
  have hp := UPre.of hs
  obtain ⟨tr,t,he,hq,hf⟩ := correct_wp hp
  refine ⟨tr,t,he,abiPreserved_of_exec (by decide +kernel) he
    ⟨fun r hr => Exec.gpr (keeps r hr) he,?_⟩,hq⟩
  exact hf.readW (r := ⟨s.gpr .rsp,8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_iv
    · exact hp.ret_data
    · exact hp.ret_scr.sub_right (Region.sub_prefix (by decide))) (by decide)

theorem ct : ConstantTime isa (cbcX86_64 false).pre (cbcX86_64 false).pub decrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx,.r8,.r9,.rsp])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1,h2,h3,h4,h5,h6,h7⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem implies : (cbcX86_64 false).Implies (Proof.AesCbc.decryptRoundsContract X86_64.abi 8) := by
  sig_implies [Proof.AesCbc.decryptRoundsContract,Spec.Cbc.aesSig,cbcX86_64,modeX86_64,cbcMode,
    ciphOf,cbc,cts,X86_64.abi,X86_64.argRegs] [sat] using sat

theorem verified : Verified X86_64.target decrypt (Proof.AesCbc.decryptRoundsContract X86_64.abi 8) :=
  Verified.of_correct correct ct implies

theorem written (s : State) (tr : List Leak) (t : State)
    (hs : (Proof.AesCbc.decryptRoundsContract X86_64.abi 8).pre s) (he : Exec isa decrypt s tr t) :
    Sig.writtenWithin (X86_64.abi.withConsts []) Spec.Cbc.aesSig [("scratch",224)] s t := by
  have hp := UPre.of (implies.pre s hs)
  obtain ⟨tr',t',he',_,hf⟩ := correct_wp hp
  obtain ⟨-,rfl⟩ := Exec.det he he'
  simp [Sig.writtenWithin,X86_64.abi,X86_64.argRegs,Abi.withConsts,Spec.Cbc.aesSig,
    Sig.words,Sig.arrays,Param.words,ArgWord.bits]
  intro i hi hlo
  have hib : i < 2176 := by simpa [Elem.size] using hlo
  exact hf _ fun r hr hc => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.iv_scr _ hc (Offset.contains_base _ (by omega) (by omega))
    · exact hp.data_scr _ hc (Offset.contains_base _ (by omega) (by omega))
    · change (S s + BitVec.ofNat 64 i - S s).toNat + 1 ≤ 224 at hc
      rw [Offset.add_sub_cancel_left,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at hc
      omega

end VG.Proof.AesCbc.X86_64.VaesDecrypt

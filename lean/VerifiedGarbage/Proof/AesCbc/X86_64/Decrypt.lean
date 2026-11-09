module

public import VerifiedGarbage.Proof.AesCbc.Rounds
public import VerifiedGarbage.Impl.AesCbc.X86_64.Decrypt
public import VerifiedGarbage.Proof.AesCbc.X86_64.Verified
public import VerifiedGarbage.Proof.AesCbc.X86_64.Encrypt
public import VerifiedGarbage.Proof.AesCbc.X86_64.Loop
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Blocks
import VerifiedGarbage.Proof.AesCbc.Decrypt
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Impl.AesCbc.X86_64.Decrypt
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.Taint

-- separate module: the parallel loop and memory proofs cost more to check than their imports.

/-! # CBC decryption: independent AES rounds, sequential chaining stores -/

@[expose] public section
namespace VG.Proof.AesCbc.X86_64.Decrypt
open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Proof.Aes.X86_64.AesNi
open VG.Impl.Aes.X86_64.AesNi (at_ regs8 loadData aesDec imcKeys blocksLoad)
open VG.Impl.AesCbc.X86_64.Decrypt
open VG.Spec.Aes (bytesAt)

/-- The processed prefix and the original unprocessed ciphertext. -/
def DataInv (m₀ m : Mem) (D : Addr) (n c : Nat) (F : Nat → Spec.Aes.State) : Prop :=
  ∀ k < n, Spec.Aes.stateAt m (D + BitVec.ofNat 64 (16*k)) =
    if k < c then F k else Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16*k))

theorem original_word {m₀ m : Mem} {D : Addr} {n c k : Nat} {F : Nat → Spec.Aes.State}
    (h : DataInv m₀ m D n c F) (hk : k < n) (hc : c ≤ k) :
    m.readW (D + BitVec.ofNat 64 (16*k)) 128 = m₀.readW (D + BitVec.ofNat 64 (16*k)) 128 := by
  apply st_inj
  rw [← stateAt_eq, ← stateAt_eq, h k hk, ite_eq_right (by omega_arith)]

theorem data_write {m₀ m : Mem} {D : Addr} {n c : Nat} {F : Nat → Spec.Aes.State} {v : BitVec 128}
    (hn : 16*n ≤ 2^64) (hc : c < n) (h : DataInv m₀ m D n c F) (hv : st v = F c) :
    DataInv m₀ (m.writeW (D + BitVec.ofNat 64 (16*c)) v) D n (c+1) F := by
  intro k hk
  by_cases he : k = c
  · subst he
    rw [stateAt_eq, Mem.readW_writeW_self _ _ 16 _ (by decide), hv, ite_eq_left (by omega_arith)]
  · rw [stateAt_eq, Mem.readW_writeW_sep (Offset.disjoint D (by omega_using [he]) (by omega_arith) (by omega_arith)) (by decide),
      ← stateAt_eq, h k hk]
    by_cases hlt : k < c
    · rw [ite_eq_left hlt, ite_eq_left (by omega_arith)]
    · rw [ite_eq_right hlt, ite_eq_right (by omega_using [hlt,he])]

theorem finish_ok (b : XReg) (j : Nat) (s : State) (hb : b ≠ .xmm15)
    (hin : InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 (16*j)) 16) :
    WP isa (.block (finish b j)) s fun t =>
      t.mem = s.mem.writeW (s.gpr .rdx + BitVec.ofNat 64 (16*j)) (s.xmm b ^^^ s.xmm .xmm15) ∧
      t.xmm .xmm15 = s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 (16*j)) 128 ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.ymmHi = s.ymmHi ∧
      (∀ r, r ≠ b → r ≠ .xmm15 → t.xmm r = s.xmm r) := by
  rw [finish, WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, VG.Proof.AesCbc.X86_64.Encrypt.exec_load (by
    simp only [XOp.exec, rd_setXmm, wr_setXmm, gpr_setXmm]
    exact ⟨hin.choose, List.mem_append_right _ hin.choose_spec.1, hin.choose_spec.2⟩), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, VG.Proof.AesCbc.X86_64.Encrypt.exec_store (by
    simp only [XOp.exec, wr_setXmm, gpr_setXmm]; exact hin), WP.block_nil ?_⟩
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl, fun r h₁ h₂ => ?_⟩
  · simp only [XOp.exec, mem_setXmm, gpr_setXmm, xmm_setXmm_of_ne _ _ hb,
      xmm_setXmm_self, XBinOp.eval]
  · simp only [xmm_setXmm_self, XOp.exec, mem_setXmm, gpr_setXmm]
  · simp only [XOp.exec, xmm_setXmm_of_ne _ _ h₂, xmm_setXmm_of_ne _ _ h₁]

/-- A group is written in order, retaining each ciphertext for its successor. -/
theorem finishData_ok {m₀ : Mem} {D : Addr} {n c : Nat} {F : Nat → Spec.Aes.State}
    {chain : Nat → BitVec 128} (hn : 16*n ≤ 2^64)
    (hnext : ∀ k < n, chain (k+1) = m₀.readW (D + BitVec.ofNat 64 (16*k)) 128) :
    ∀ (rs : List XReg) (j : Nat) (s : State), rs.Nodup → .xmm15 ∉ rs →
    s.gpr .rdx = D + BitVec.ofNat 64 (16*c) → c+j+rs.length ≤ n →
    (⟨D,16*n⟩ : Region) ∈ s.wr → DataInv m₀ s.mem D n (c+j) F →
    s.xmm .xmm15 = chain (c+j) →
    (∀ k (h : k < rs.length), st (s.xmm rs[k] ^^^ chain (c+j+k)) = F (c+j+k)) →
    WP isa (.block (finishData rs j)) s fun t =>
      DataInv m₀ t.mem D n (c+j+rs.length) F ∧ t.xmm .xmm15 = chain (c+j+rs.length) ∧
      Frame [⟨D,16*n⟩] s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.ymmHi = s.ymmHi ∧
      (∀ r, r ≠ .xmm15 → r ∉ rs → t.xmm r = s.xmm r)
  | [], _, s, _, _, _, _, _, hd, hx, _ =>
    WP.block_nil ⟨hd,hx,Frame.refl _ _,rfl,rfl,rfl,rfl,fun _ _ _ => rfl⟩
  | b::bs, j, s, hnd, h15, hg, hc, hw, hd, hx, hv => by
    have hb : b ≠ .xmm15 := fun h => h15 (h ▸ List.mem_cons_self)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have h15' : .xmm15 ∉ bs := fun h => h15 (List.mem_cons_of_mem _ h)
    simp only [List.length_cons] at hc
    have addr : s.gpr .rdx + BitVec.ofNat 64 (16*j) = D + BitVec.ofNat 64 (16*(c+j)) := by
      rw [hg, Offset.add_add_eq D (c := 16*(c+j)) (by omega_arith)]
    rw [finishData, WP.block_append_iff]
    refine WP.mono (finish_ok b j s hb (by
      rw [addr]; exact ⟨_, hw, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩))
      fun t ⟨hm,hx',hg',hr,hw',yh,ho⟩ => ?_
    rw [addr] at hm hx'
    have hv0 : st (s.xmm b ^^^ s.xmm .xmm15) = F (c+j) := by
      rw [hx]; exact hv 0 (by simp)
    have hd' := data_write hn (by omega_arith) hd hv0
    rw [← hm] at hd'
    have hchain : t.xmm .xmm15 = chain (c+(j+1)) := by
      rw [hx', original_word hd (by omega_arith) (by omega_arith), ← hnext (c+j) (by omega_arith)]
      congr 1
    have hf : Frame [⟨D,16*n⟩] s.mem t.mem := by
      rw [hm]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
    refine WP.mono (finishData_ok (m₀ := m₀) (D := D) (n := n) (c := c) (F := F) (chain := chain) hn hnext bs (j+1) t (List.nodup_cons.mp hnd).2 h15'
      (by rw [hg']; exact hg) (by omega_arith) (hw' ▸ hw) (by simpa [Nat.add_assoc] using hd') hchain
      (fun k hk => by
        rw [ho _ (fun h => hbs (h ▸ List.getElem_mem hk)) (fun h => h15' (h ▸ List.getElem_mem hk)),
          show c+(j+1)+k=c+j+(k+1) by omega_arith]
        exact hv (k+1) (by simp; omega_arith))) fun u ⟨hu,hx'',hf',hg'',hr',hw'',yh',ho'⟩ => ?_
    have he : c+(j+1)+bs.length = c+j+(b::bs).length := by simp; omega_arith
    rw [he] at hu hx''
    exact ⟨hu,hx'',hf.trans hf',hg''.trans hg',hr'.trans hr,hw''.trans hw',yh'.trans yh,fun r h₁ h₂ =>
      (ho' r h₁ (fun h => h₂ (List.mem_cons_of_mem _ h))).trans
        (ho r (fun h => h₂ (h ▸ List.mem_cons_self)) h₁)⟩

def chaining (s₀ : State) : Nat → BitVec 128
  | 0 => s₀.mem.readW (Iv s₀) 128
  | k+1 => s₀.mem.readW (blk s₀ k) 128

def output (s₀ : State) (k : Nat) : Spec.Aes.State :=
  Vector.ofFn fun i =>
    (Spec.Aes.invCipher (R s₀) (wK s₀) (Spec.Aes.stateAt s₀.mem (blk s₀ k))).getD i.1 0 ^^^
      byte (chaining s₀ k) i.1

structure Inv (s₀ : State) (c p : Nat) (s : State) : Prop where
  le : c ≤ N s₀
  keys : DKeys (R s₀) (wK s₀) s
  rdi : s.gpr .rdi = W s₀
  rsi : s.gpr .rsi = s₀.gpr .rsi
  r8 : s.gpr .r8 = S s₀
  r10 : s.gpr .r10 = W s₀ + BitVec.ofNat 64 (16 * R s₀)
  r11 : s.gpr .r11 = Iv s₀
  rdx : s.gpr .rdx = blk s₀ p
  rcx : s.gpr .rcx = BitVec.ofNat 64 (N s₀-p)
  chain : s.xmm .xmm15 = chaining s₀ c
  data : DataInv s₀.mem s.mem (Dp s₀) (N s₀) c (output s₀)
  frame : Frame [dataR s₀, ⟨S s₀,224⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem keys_stable {s₀ s t : State} (hp : UPre s₀) (h : DKeys (R s₀) (wK s₀) s)
    (hdi : s.gpr .rdi = W s₀) (h8 : s.gpr .r8 = S s₀)
    (hg : t.gpr = s.gpr) (hr : t.rd = s.rd) (hw : t.wr = s.wr)
    (hf : Frame [dataR s₀] s.mem t.mem) : DKeys (R s₀) (wK s₀) t := by
  refine Ecb.dkeys_congr h (by rw [hg]) (by rw [hg]) hr hw ?_ ?_
  · rw [hdi]
    exact bytesAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.sch_data.sub_left (Region.sub_prefix (by rcases hp.rounds with h | h | h <;> omega_arith))) (by
        rcases hp.rounds with h | h | h <;> omega_arith)
  · intro j h₁ h₂
    rw [h8, ofInt_natCast]
    exact hf.readW (r := ⟨S s₀ + BitVec.ofNat 64 (16*j),16⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_scr.sub_right (Offset.sub_base _ (by rcases hp.rounds with h | h | h <;> omega_arith))).symm) (by decide)

theorem group_ok {s₀ s : State} (hp : UPre s₀) (rs : List XReg)
    (hrs : rs = regs8 ∨ rs = [.xmm0]) {c : Nat} (hc : c+rs.length ≤ N s₀)
    (hI : Inv s₀ c c s) (after : List Instr) {Q : State → Prop}
    (hQ : ∀ t, Inv s₀ (c+rs.length) c t → WP isa (.block after) t Q) :
    WP isa (group rs after) s Q := by
  obtain ⟨hnd,h8⟩ := Ecb.regs_nodup rs hrs
  have h15 : .xmm15 ∉ rs := by rcases hrs with rfl | rfl <;> decide
  have hw := hp.data_wrap
  have addr (t : State) (ht : t.gpr .rdx = s.gpr .rdx) (k : Nat) :
      t.gpr .rdx + BitVec.ofInt 64 ((16*(0+k):Nat):Int) = blk s₀ (c+k) := by
    rw [ht,hI.rdx,ofInt_natCast,blk,blk,Offset.add_add_eq _ (c := 16*(c+k)) (by omega_arith)]
  have addr' (k : Nat) : s.gpr .rdx + BitVec.ofNat 64 (16*(0+k)) = blk s₀ (c+k) := by
    rw [← addr s rfl k,ofInt_natCast]
  refine WP.seq (WP.mono (loadData_ok rs 0 s hnd (fun k hk => by
    rw [addr s rfl k,hI.rd,hI.wr,hp.rd,hp.wr]
    exact ⟨dataR s₀,by simp,Offset.contains_base _ (by omega_arith) (by omega_arith)⟩))
    fun u ⟨hl,gl,ml,rl,wl,xl⟩ => ?_)
  have hku : DKeys (R s₀) (wK s₀) u :=
    hI.keys.of_frame ⟨gl,ml,rl,wl,xl⟩
  refine WP.seq (WP.mono (aesDec_ok rs hnd h8 hp.rounds u hku
    (by rw [gl,hI.rsi]; simp) (by rw [gl,hI.r10,hI.rdi])) fun v ⟨ha,fa⟩ => ?_)
  have gv : v.gpr = s.gpr := fa.gpr.trans gl
  have mv : v.mem = s.mem := fa.mem.trans ml
  have hx : v.xmm .xmm15 = chaining s₀ c := by rw [fa.xmm _ (by simp [h15]),xl _ h15,hI.chain]
  rw [WP.block_append_iff]
  refine WP.mono (finishData_ok (m₀ := s₀.mem) (D := Dp s₀) (n := N s₀) (c := c)
    (F := output s₀) (chain := chaining s₀) (by omega_arith) (fun _ _ => rfl) rs 0 v hnd h15
    (by rw [gv,hI.rdx]) (by simpa using hc)
    (by rw [fa.wr,wl,hI.wr,hp.wr]; simp) (by simpa [mv] using hI.data)
    (by simpa using hx) (fun k hk => by
      have he := ha _ (List.getElem_mem hk)
      rw [hl k hk,← ofInt_natCast (16*(0+k))] at he
      rw [addr s rfl k,hI.data _ (by omega_arith),ite_eq_right (by omega_arith)] at he
      apply st_ext
      intro i hi
      rw [getD_st _ hi,byte_xor,← getD_st _ hi,he]
      change _ = (Vector.ofFn fun i =>
        (Spec.Aes.invCipher (R s₀) (wK s₀) (Spec.Aes.stateAt s₀.mem (blk s₀ (c+0+k)))).getD i.1 0 ^^^
          byte (chaining s₀ (c+0+k)) i.1).getD i 0
      rw [getD_ofFn hi]; rfl)) fun t ⟨hd,hchain,hf,hg,hr,hw,_,ho⟩ => ?_
  have gt : t.gpr = s.gpr := hg.trans gv
  have rt : t.rd = s.rd := hr.trans (fa.rd.trans rl)
  have wt : t.wr = s.wr := hw.trans (fa.wr.trans wl)
  rw [mv] at hf
  refine hQ t ⟨hc,keys_stable hp hI.keys hI.rdi hI.r8 gt rt wt hf,
    by rw [gt]; exact hI.rdi,by rw [gt]; exact hI.rsi,by rw [gt]; exact hI.r8,
    by rw [gt]; exact hI.r10,by rw [gt]; exact hI.r11,by rw [gt]; exact hI.rdx,
    by rw [gt]; exact hI.rcx,by simpa using hchain,by simpa using hd,
    hI.frame.trans (hf.mono (by simp)),rt.trans hI.rd,wt.trans hI.wr⟩

/-- The eight-block body. -/
theorem body8_ok {s₀ : State} (hp : UPre s₀) {c : Nat} (hc : c + 8 ≤ N s₀) {s : State} (hI : Inv s₀ c c s) :
    WP isa blocks8 s fun s' => Inv s₀ (c + 8) (c + 8) s' ∧
      s'.cf = some (decide (N s₀ - (c + 8) < 8)) := by
  have hn : 16*N s₀ ≤ 2^64 := by have := hp.data_wrap; omega_arith
  refine group_ok hp regs8 (.inl rfl) hc hI _ fun s₁ hI₁ => ?_
  have e128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  have hrdx := hI₁.rdx
  have hrcx := hI₁.rcx
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e128, e8, hrdx, hrcx,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have hsub : BitVec.ofNat 64 (N s₀ - c) - 8 = BitVec.ofNat 64 (N s₀ - (c + 8)) := by
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
  simp only [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show N s₀ - (c + 8) < 2 ^ 64 by omega_arith),
    show (8 : BitVec 64).toNat = 8 from rfl]

/-- The one-block body. -/
theorem body1_ok {s₀ : State} (hp : UPre s₀) {c : Nat} (hc : c < N s₀) {s : State} (hI : Inv s₀ c c s) :
    WP isa blocks1 s fun s' => Inv s₀ (c + 1) (c + 1) s' ∧
      s'.zf = some (decide (N s₀ - (c + 1) = 0)) := by
  have hn : 16*N s₀ ≤ 2^64 := by have := hp.data_wrap; omega_arith
  refine group_ok hp [.xmm0] (.inr rfl) hc hI _ fun s₁ hI₁ => ?_
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  have hrdx := hI₁.rdx
  have hrcx := hI₁.rcx
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e16, e1, hrdx, hrcx,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have hsub : BitVec.ofNat 64 (N s₀ - c) - 1 = BitVec.ofNat 64 (N s₀ - (c + 1)) := by
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
  rw [hsub, Ecb.beq_ofNat_zero' (by omega_arith)]

theorem test_ok {s₀ : State} (hp : UPre s₀) {c : Nat} {s : State} (hI : Inv s₀ c c s) :
    WP isa (.block [.alu .test .rcx (.reg .rcx)]) s fun s' =>
      Inv s₀ c c s' ∧ s'.zf = some (decide (N s₀ - c = 0)) := by
  have hn : 16*N s₀ ≤ 2^64 := by have := hp.data_wrap; omega_arith
  have hrcx := hI.rcx
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, hrcx, BitVec.and_self, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨{ hI with keys := hI.keys.of_frame (rs := []) ⟨rfl,rfl,rfl,rfl,fun _ _ => rfl⟩ },
    by rw [Ecb.beq_ofNat_zero' (by omega_arith)]⟩

/-- The blocks left after `c`, eight and then one at a time. -/
theorem tail_ok {s₀ : State} (hp : UPre s₀) {c₀ : Nat} {s₁ : State} (hI₁ : Inv s₀ c₀ c₀ s₁)
    (hcf : s₁.cf = some (decide (N s₀ - c₀ < 8))) :
    WP isa tail s₁ (Inv s₀ (N s₀) (N s₀)) := by
  have hn : 16*N s₀ ≤ 2^64 := by have := hp.data_wrap; omega_arith
  refine WP.seq (WP.mono (Q := fun s => ∃ c, N s₀ - c < 8 ∧ Inv s₀ c c s) ?_
    fun s₂ ⟨c, hc, hI₂⟩ => ?_)
  · refine WP.ite (decide (N s₀ - c₀ < 8)) (by simp [eval, hcf]) (fun h => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨c₀, by simpa using h, hI₁⟩
    · let I8 : Nat → State → Prop := fun m s => ∃ c, m = N s₀ - c ∧ c + 8 ≤ N s₀ ∧ Inv s₀ c c s
      have hstep : ∀ m s, I8 m s → WP isa blocks8 s (fun s' =>
          (eval .ae s' = some false ∧ ∃ c, N s₀ - c < 8 ∧ Inv s₀ c c s') ∨
          (eval .ae s' = some true ∧ ∃ m' < m, I8 m' s')) := by
        rintro m s ⟨c, rfl, hc, hI⟩
        refine WP.mono (body8_ok hp hc hI) fun s' ⟨hI', hcf'⟩ => ?_
        by_cases hlt : N s₀ - (c + 8) < 8
        · exact .inl ⟨by simp [eval, hcf', hlt], c + 8, hlt, hI'⟩
        · exact .inr ⟨by simp [eval, hcf', hlt], N s₀ - (c + 8), by omega_arith, c + 8, rfl, by omega_arith, hI'⟩
      exact WP.loop (M := isa) I8 hstep (N s₀ - c₀) s₁ ⟨c₀, rfl, by simp at h; omega_arith, hI₁⟩
  refine WP.seq (WP.mono (test_ok hp hI₂) fun s₃ ⟨hI₃, hzf⟩ => ?_)
  refine WP.ite (decide (N s₀ - c = 0)) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have : c = N s₀ := by have := hI₃.le; simp at h; omega_arith
    exact WP.block_nil (this ▸ hI₃)
  · let I1 : Nat → State → Prop := fun m s => ∃ c, m = N s₀ - c ∧ c < N s₀ ∧ Inv s₀ c c s
    have hstep : ∀ m s, I1 m s → WP isa blocks1 s (fun s' =>
        (eval .ne s' = some false ∧ Inv s₀ (N s₀) (N s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, I1 m' s')) := by
      rintro m s ⟨c, rfl, hc, hI⟩
      refine WP.mono (body1_ok hp hc hI) fun s' ⟨hI', hzf'⟩ => ?_
      by_cases hlast : N s₀ - (c + 1) = 0
      · have : c + 1 = N s₀ := by omega_arith
        exact .inl ⟨by simp [eval, hzf', hlast], this ▸ hI'⟩
      · exact .inr ⟨by simp [eval, hzf', hlast], N s₀ - (c + 1), by omega_arith, c + 1, rfl, by omega_arith, hI'⟩
    have hlt : c < N s₀ := by have := hI₃.le; simp at h; omega_arith
    exact WP.loop (M := isa) I1 hstep (N s₀ - c) s₃ ⟨c, rfl, hlt, hI₃⟩

def adapted (s : State) : State :=
  ((((s.setReg .r11 (s.gpr .rdx)).setReg .rdx (s.gpr .rcx)).setReg .rcx (s.gpr .r8)).setReg
    .r8 (s.gpr .r9)).setXmm .xmm15 (s.mem.readW (s.gpr .rdx) 128)

theorem adapt_ok {s : State} (hp : UPre s) : WP isa (.block adapt) s (fun t => t = adapted s) := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .rdx) 16 := by
    rw [hp.rd,hp.wr]
    exact ⟨ivR s,by simp,Region.contains_self _ _⟩
  have haz (p : Addr) : p + BitVec.ofInt 64 ((0 : Nat) : Int) = p := by bv_omega
  apply WP.of_runBlock
  simp only [adapt,runBlock_cons,runStep_some,runBlock_nil,exec,isa,readSrc,Option.map_some,
    at_,State.ea,gpr_setReg,mem_setReg,rd_setReg,wr_setReg,reduceCtorEq,ite_true,ite_false,
    haz,State.load128,hin,Option.some.injEq,exists_eq_left']
  rfl

theorem setup_ok {s₀ : State} (hp : UPre s₀) :
    WP isa (.seq (.block adapt) (.seq imcKeys (.block blocksLoad))) s₀ fun s =>
      Inv s₀ 0 0 s ∧ s.cf = some (decide (N s₀ < 8)) := by
  refine WP.seq (WP.mono (adapt_ok hp) fun a ha => ?_)
  subst ha
  let a := adapted s₀
  have ga : ∀ r, a.gpr r = (match r with
      | .r11 => Iv s₀ | .rdx => Dp s₀ | .rcx => s₀.gpr .r8 | .r8 => S s₀ | _ => s₀.gpr r) := by
    intro r
    simp only [a,adapted,gpr_setXmm,gpr_setReg]
    cases r <;> rfl
  have ma : a.mem = s₀.mem := by simp only [a,adapted,mem_setXmm,mem_setReg]
  have ra : a.rd = s₀.rd := rfl
  have wa : a.wr = s₀.wr := rfl
  have hs : InRegions a.wr (a.gpr .r8) 2048 := by
    rw [wa,ga,hp.wr]
    exact ⟨scrR s₀,by simp,by simpa using Offset.contains_base (S s₀) (d := 0) (n := 2048) (k := 2176) (by decide) (by decide)⟩
  have hsep : (⟨a.gpr .rdi,240⟩ : Region).Disjoint ⟨a.gpr .r8,2048⟩ := by
    simp only [ga]; exact hp.sch_scr.sub_right (Region.sub_prefix (by decide))
  have hK : Keys (R s₀) (wK s₀) a := by
    refine ⟨?_,by rcases hp.rounds with h | h | h <;> omega_arith,?_⟩
    · rw [ma,ga]
    · intro j hj
      rw [ra,wa,ga,hp.rd,hp.wr,ofInt_natCast]
      exact ⟨schR s₀,by simp,Offset.contains_base _ (by rcases hp.rounds with h | h | h <;> omega_arith) (by
        rcases hp.rounds with h | h | h <;> omega_arith)⟩
  refine WP.seq (WP.mono (imcKeys_ok hp.rounds (by rw [ga]; exact rsi_ofNat s₀) hs
    (by rw [ga,ra,wa,hp.rd,hp.wr]; simp) hsep) fun u ⟨js,hi,hjs⟩ => ?_)
  have hD := dKeys_of_imc hK hs hsep hi hjs
  refine WP.mono (Ecb.blocksLoad_ok u) fun v ⟨h10,hg,hm,hr,hw,hx,hcf⟩ => ?_
  have hg' (r : Reg) (hn : r ≠ .r10) : v.gpr r = a.gpr r := by rw [hg r hn,hi.gpr]
  have frameU : Frame [dataR s₀,⟨S s₀,224⟩] s₀.mem u.mem := by
    have hf := hi.lo
    rw [ma,ga] at hf
    exact hf.mono (by simp)
  have keysV : DKeys (R s₀) (wK s₀) v :=
    Ecb.dkeys_congr hD (hg _ (by decide)) (hg _ (by decide)) hr hw
      (by rw [hm]) (fun _ _ _ => by rw [hm])
  refine ⟨⟨Nat.zero_le _,keysV,by rw [hg' _ (by decide),ga],by rw [hg' _ (by decide),ga],
    by rw [hg' _ (by decide),ga],?_,by rw [hg' _ (by decide),ga],?_,?_,?_,?_,?_,?_,?_⟩,?_⟩
  · rw [h10,hi.gpr,ga,ga]
  · rw [hg' _ (by decide),ga]; simp [blk]
  · rw [hg' _ (by decide),ga]; simp [N]
  · rw [hx,hi.xmm _ (by decide)]
    rfl
  · intro k hk
    rw [hm]
    have hd : (⟨blk s₀ k,16⟩ : Region).Disjoint ⟨S s₀,2048⟩ :=
      (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))
    rw [stateAt_eq,stateAt_eq]
    have hf := hi.frame
    rw [ma,ga] at hf
    rw [hf.readW (r := ⟨blk s₀ k,16⟩) (Region.contains_self _ _)
      (by simpa using hd) (by decide),ite_eq_right (Nat.not_lt_zero _)]
  · rw [hm]; exact frameU
  · rw [hr,hi.rd,ra]
  · rw [hw,hi.wr,wa]
  · rw [hcf,hi.gpr,ga]

theorem list_getD {α : Type} {xs : List α} {k : Nat} {d : α} (hk : k < xs.length) :
    xs.getD k d = xs[k] := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,Option.getD_some]

theorem vector_listD (v : Spec.Aes.State) (i : Nat) (hi : i < 16) :
    v.toList.getD i 0 = v.getD i 0 := by
  rw [list_getD (by simpa using hi),Vector.getElem_toList]
  simp [Vector.getD,hi]

theorem chaining_bytes (s₀ : State) (k : Nat) (hk : k ≤ N s₀) :
    (st (chaining s₀ k)).toList = Spec.Cbc.next (iv0 s₀) ((blks s₀).take k) := by
  cases k with
  | zero => simp only [chaining,← stateAt_eq,List.take_zero]; exact (bytesAt_toList _ _).symm
  | succ k =>
    rw [next_take_succ _ _ k (by rw [length_blocksAt]; omega),
      list_getD (by rw [length_blocksAt]; omega),getElem_blocksAt (hk := by omega)]
    exact (congrArg Vector.toList (stateAt_eq _ _).symm).trans (bytesAt_toList _ _).symm

theorem block_bytes (s₀ : State) (k : Nat) (hk : k < N s₀) :
    (output s₀ k).toList =
      (Spec.Cbc.decrypt (Spec.Cbc.aesInvWith (R s₀) (wK s₀)) (iv0 s₀) (blks s₀)).getD k [] := by
  rw [decrypt_getD _ _ _ k (by rw [length_blocksAt]; exact hk),
    list_getD (by rw [length_blocksAt]; exact hk),getElem_blocksAt (hk := hk),
    aesInvWith_state,← chaining_bytes _ _ (Nat.le_of_lt hk)]
  apply Proof.Cmac.ext16 (by simp) (by simp [Spec.Cbc.xor])
  intro i hi
  rw [vector_listD _ _ hi]
  rw [xor_eq,Proof.Cmac.getD_xor (by simp) (by simpa using hi)]
  rw [vector_listD _ _ hi,vector_listD _ _ hi]
  rw [getD_st _ hi]
  exact getD_ofFn hi

theorem data_done {s₀ : State} {m : Mem}
    (hd : DataInv s₀.mem m (Dp s₀) (N s₀) (N s₀) (output s₀)) :
    Spec.Cbc.blocksAt m (Dp s₀) (N s₀) =
      Spec.Cbc.decrypt (Spec.Cbc.aesInvWith (R s₀) (wK s₀)) (iv0 s₀) (blks s₀) := by
  apply List.ext_getElem
  · simp [length_decrypt,length_blocksAt]
  · intro k hk _
    have hk' : k < N s₀ := by simpa [length_blocksAt] using hk
    rw [getElem_blocksAt _ _ hk',bytesAt_toList,hd k hk',ite_eq_left hk',block_bytes _ _ hk',
      list_getD (by simp [length_decrypt,length_blocksAt]; exact hk')]

theorem finish_wp {s₀ s : State} (hp : UPre s₀) (hI : Inv s₀ (N s₀) (N s₀) s) :
    WP isa (.block [.movdquStore (at_ .r11 0) .xmm15]) s fun t =>
      (cbcX86_64 false).post s₀ t ∧ Frame [ivR s₀,dataR s₀,⟨S s₀,224⟩] s₀.mem t.mem := by
  rw [WP.block_cons_iff]
  refine ⟨_,VG.Proof.AesCbc.X86_64.Encrypt.exec_store (by
    rw [hI.wr,hI.r11,hp.wr,BitVec.add_zero]
    exact ⟨ivR s₀,by simp,Region.contains_self _ _⟩),WP.block_nil ?_⟩
  have fs : Frame [ivR s₀] s.mem (s.mem.writeW (Iv s₀) (s.xmm .xmm15)) :=
    (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  simp only [hI.r11,BitVec.add_zero]
  refine ⟨⟨?_,?_⟩,(hI.frame.mono (by simp)).trans (fs.mono (by simp))⟩
  · change Spec.Cbc.blocksAt (s.mem.writeW (Iv s₀) (s.xmm .xmm15)) (Dp s₀) (N s₀) = _
    have hb : Spec.Cbc.blocksAt (s.mem.writeW (Iv s₀) (s.xmm .xmm15)) (Dp s₀) (N s₀) =
        Spec.Cbc.blocksAt s.mem (Dp s₀) (N s₀) := by
      apply List.map_congr_left
      intro k hk
      exact bytesAt_frame fs (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.iv_data.symm.sub_left (UPre.data_sub (List.mem_range.mp hk))) (by decide)
    rw [hb,data_done hI.data]
    rfl
  · change bytesAt (s.mem.writeW (Iv s₀) (s.xmm .xmm15)) (Iv s₀) 16 = _
    rw [← VG.Proof.AesCbc.X86_64.Encrypt.bytes_read,Mem.readW_writeW_self _ _ 16 _ (by decide),hI.chain]
    change (st (chaining s₀ (N s₀))).toList = _
    rw [chaining_bytes _ _ (Nat.le_refl _),List.take_of_length_le (by simp [Spec.Cbc.blocksAt])]
    rfl

theorem correct_wp {s₀ : State} (hp : UPre s₀) : WP isa decrypt s₀ fun t =>
    (cbcX86_64 false).post s₀ t ∧ Frame [ivR s₀,dataR s₀,⟨S s₀,224⟩] s₀.mem t.mem := by
  change WP isa (.seq (.seq (.block adapt) (.seq imcKeys (.block blocksLoad)))
    (.seq tail (.block [.movdquStore (at_ .r11 0) .xmm15]))) s₀ _
  refine WP.seq (WP.mono (setup_ok hp) fun s ⟨hI,hcf⟩ => ?_)
  refine WP.seq (WP.mono (tail_ok hp hI (by simpa using hcf)) fun s' hI' => finish_wp hp hI')

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

end VG.Proof.AesCbc.X86_64.Decrypt

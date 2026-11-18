module

public import VerifiedGarbage.Proof.AesSiv.X86_64.Seal
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesSiv.X86_64.CmacOf
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.AesSiv.X86_64.Seal
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesSiv.X86_64.CmacOf
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.AesSiv.X86_64.Open
public import VerifiedGarbage.Spec.Siv.Contract
import VerifiedGarbage.Proof.AesSiv.X86_64.Call
import VerifiedGarbage.Proof.AesSiv.X86_64.Common
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.AesSiv.X86_64.Open
meta import VerifiedGarbage.Spec.Siv.Contract
meta import VerifiedGarbage.Proof.AesSiv.X86_64.Call
meta import VerifiedGarbage.Proof.AesSiv.X86_64.Common
meta import VerifiedGarbage.Proof.Cmac.Block
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.AesSiv.X86_64.Crypt
import VerifiedGarbage.Proof.AesSiv.Ctr32
meta import VerifiedGarbage.Proof.AesSiv.X86_64.Crypt
meta import VerifiedGarbage.Proof.AesSiv.Ctr32
meta import VerifiedGarbage.Impl.AesSiv.X86_64
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.TCB.X86_64.Isa
meta import VerifiedGarbage.TCB.X86_64.State
public import VerifiedGarbage.Proof.AesSiv.X86_64.Ctr
meta import VerifiedGarbage.Proof.AesSiv.X86_64.Ctr
meta import VerifiedGarbage.TCB.X86_64.Gpr
meta import VerifiedGarbage.TCB.X86_64.Target

/-! ### `AesSiv.X86_64.CryptCT`, which only this module used -/

section

/-! ### `AesSiv.X86_64.CtrCT`, which only this module used -/

section

/-!
# AES-SIV on x86-64: CTR is constant time

`ctrWhole`'s call of `vg_aes_ctr32` takes the pointers and `k`, which the
code computes from the length alone, so its arguments are the same in both
runs and the code around it passes the taint analysis (`whole_rel`); both
runs then take the same branch, on the bytes left (`ctr_rel'`). After it,
every block's pointers and lengths are public (`r13`, `r14`), so the code
around the call of `vg_aes_ctr32` passes the taint analysis, and the call's
arguments are the same in both runs (`ctr_rel` of `CmacAes.X86_64`). Both
runs leave the loop after the same block, the last one (`ctr_tail`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64 VG.WriteBytes
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (bytesAt_frame zero2 zero2_bytes)
open VG.Proof.CmacAes.Stream.X86_64 (copyMem_frame toNat_ofNat)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

variable {g : Lay} {s₀ : State} {C D P W : Addr} {R L : Nat}

/-- The registers of block `i`. -/
structure CR (s₀ : State) (C D P W : Addr) (R L i : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = C
  rbp : s.gpr .rbp = BitVec.ofNat 64 R
  r12 : s.gpr .r12 = D
  r13 : s.gpr .r13 = P + BitVec.ofNat 64 (16 * i)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (L - 16 * i)
  r15 : s.gpr .r15 = W
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem CR.keep {s₀ s s' : State} {C D P W : Addr} {R L i : Nat} (h : CR s₀ C D P W R L i s)
    (hs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    CR s₀ C D P W R L i s' :=
  ⟨by rw [hs _ (by decide), h.rbx], by rw [hs _ (by decide), h.rbp], by rw [hs _ (by decide), h.r12],
    by rw [hs _ (by decide), h.r13], by rw [hs _ (by decide), h.r14], by rw [hs _ (by decide), h.r15],
    by rw [hs _ (by decide), h.rsp], by rw [hrd, h.rd], by rw [hwr, h.wr]⟩

theorem CInv.cr {m₀ : Mem} {q x : List Byte} {i : Nat} {s : State} (hi : CInv g s₀ C D P W R L m₀ q x i s) :
    CR s₀ C D P W R L i s :=
  ⟨hi.rbx, hi.rbp, hi.r12, hi.r13, hi.r14, hi.r15, hi.rsp, hi.rd, hi.wr⟩

theorem cr_agree {s₀' a b : State} {i : Nat} (hq : s₀.gpr .rsp = s₀'.gpr .rsp) (ha : CR s₀ C D P W R L i a)
    (hb : CR s₀' C D P W R L i b) :
    taint.Agree (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp]) a b := by
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ha.rbx, hb.rbx]
  · rw [ha.rbp, hb.rbp]
  · rw [ha.r12, hb.r12]
  · rw [ha.r13, hb.r13]
  · rw [ha.r14, hb.r14]
  · rw [ha.r15, hb.r15]
  · rw [ha.rsp, hb.rsp, hq]

theorem ctrPre_wp (h : Env g s₀ C D P W R L) {i : Nat} {s : State} (hr : CR s₀ C D P W R L i s) :
    WP isa (.block (ctrPre g.x)) s fun t => CA g t (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96)
      (W + BitVec.ofNat 64 80) W R ∧ CR s₀ C D P W R L i t := by
  have hwW := h.wW
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, r9₁, g₁, m₁, rd₁, wr₁⟩ := ctrPre_ok h hr.rbx hr.rbp hr.r15 hr.rd hr.wr
  have hz : Spec.Aes.bytesAt s₁.mem (W + BitVec.ofNat 64 80) 16 = Spec.Cmac.zeros 16 := by
    rw [m₁, bytesAt_frame (copyMem_frame _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint W (by omega_using []) (by omega_using []) (by omega_using []))
      (by decide), zero2_bytes]
  have hr₁ := hr.keep g₁ rd₁ wr₁
  exact WP.of_runBlock ⟨s₁, run₁, h.cargs hr₁.rd hr₁.wr hr₁.rsp rdi₁ rsi₁ rdx₁ rcx₁ r8₁ r9₁ hz, hr₁⟩

/-- A block is constant time. -/
theorem body_rel (v : Ctr32Impl) (K : CCalls v g) {s₀' : State} (h : Env g s₀ C D P W R L) (h' : Env g s₀' C D P W R L)
    (hq : s₀.gpr .rsp = s₀'.gpr .rsp) (i : Nat) :
    RelCT isa (fun a b => CR s₀ C D P W R L i a ∧ CR s₀' C D P W R L i b) (ctrBody g.x v.callee) fun _ _ => True := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp]) (.block (ctrPre g.x))
      hc).isSome = true := by rcases h.lay with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.seq ctrMin (.seq xorBytes (.block ctrPost))) hc).isSome = true := ⟨_, by taint_decide⟩
  have r₁ := (RelCT.taint (A := taint) (P := fun a b => CR s₀ C D P W R L i a ∧ CR s₀' C D P W R L i b) _
    (fun a b hab => cr_agree hq hab.1 hab.2) hA).wp
    (F₁ := fun (t : State) => CA g t (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96)
      (W + BitVec.ofNat 64 80) W R ∧ CR s₀ C D P W R L i t)
    (F₂ := fun (t : State) => CA g t (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96)
      (W + BitVec.ofNat 64 80) W R ∧ CR s₀' C D P W R L i t)
    fun a b hab => ⟨ctrPre_wp h hab.1, ctrPre_wp h' hab.2⟩
  have r₂ := (K.ctrRel (P := fun (a b : State) => (CA g a (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96)
      (W + BitVec.ofNat 64 80) W R ∧ CR s₀ C D P W R L i a) ∧
      CA g b (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96)
      (W + BitVec.ofNat 64 80) W R ∧ CR s₀' C D P W R L i b)
    fun a b hab => ⟨_, _, _, _, _, hab.1.1, hab.2.1, by rw [hab.1.2.rsp, hab.2.2.rsp, hq]⟩).wp
    (F₁ := CR s₀ C D P W R L i) (F₂ := CR s₀' C D P W R L i)
    fun a b hab => ⟨WP.mono (K.ctr hab.1.1) fun _ p => hab.1.2.keep p.saved p.rd p.wr,
      WP.mono (K.ctr hab.2.1) fun _ p => hab.2.2.keep p.saved p.rd p.wr⟩
  have r₃ := RelCT.taint (A := taint) (P := fun a b => CR s₀ C D P W R L i a ∧ CR s₀' C D P W R L i b) _
    (fun a b hab => cr_agree hq hab.1 hab.2) hB
  exact (r₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((r₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq r₃)

/-- Block `i` of a run, with the slots of the data and its length as at the start. -/
def CI (g : Lay) (s₀ : State) (C D P W : Addr) (R L i : Nat) (s : State) : Prop :=
  16 * i < L ∧ ∃ m₀ q x, CInv g s₀ C D P W R L m₀ q x i s ∧ m₀.readW (W + BitVec.ofNat 64 dataOff) 64 = P ∧
    m₀.readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L

/-- After the loop: what the reload of the pointer and the length needs. -/
structure CEnd (s₀ : State) (C D P W : Addr) (R L : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = C
  rbp : s.gpr .rbp = BitVec.ofNat 64 R
  r12 : s.gpr .r12 = D
  r15 : s.gpr .r15 = W
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  d208 : s.mem.readW (W + BitVec.ofNat 64 dataOff) 64 = P
  d216 : s.mem.readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L

theorem slot_keep (h : Env g s₀ C D P W R L) {m m' : Mem} (hf : Frame (ctrRegions g W P L (s₀.gpr .rsp)) m m') {d : Nat}
    (hd : 208 ≤ d) (hd' : d + 8 ≤ 256) : m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 := by
  have hwW := h.wW
  refine hf.readW (w := 64) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.p_w.symm.sub_left (h.sW (by omega_using [hd']))
  · exact Offset.disjoint W (by omega_using [hd]) (by omega_using [hd']) (by omega_using [])
  · exact h.dX (by omega_using [hd'])
  · exact (h.stk_w.sub_right (h.sW (by omega_using [hd']))).symm

/-- What a block leaves, for the loop: the last block, or the next one. -/
def BPost (g : Lay) (s₀ : State) (C D P W : Addr) (R L i : Nat) (s : State) : Prop :=
  (L - 16 * i ≤ 16 ∧ s.zf = some true ∧ CEnd s₀ C D P W R L s) ∨
    (16 < L - 16 * i ∧ s.zf = some false ∧ CI g s₀ C D P W R L (i + 1) s)

theorem body_wp (v : Ctr32Impl) (K : CCalls v g) (h : Env g s₀ C D P W R L) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {i : Nat} {s : State} (hs : CI g s₀ C D P W R L i s) :
    WP isa (ctrBody g.x v.callee) s (BPost g s₀ C D P W R L i) := by
  obtain ⟨hiL, m₀, q, x, hi, h208, h216⟩ := hs
  refine ctr_head v K h hcp hi fun t₃ hh => WP.mono (ctr_tail h hPw hi hiL hh) fun t ht => ?_
  rcases ht with ⟨hc, hz, hd⟩ | ⟨hc, hz, hi'⟩
  · exact Or.inl ⟨hc, hz, ⟨hd.rbx, hd.rbp, hd.r12, hd.r15, hd.rsp, hd.rd, hd.wr,
      by rw [slot_keep h hd.frame (by decide) (by decide)]; exact h208,
      by rw [slot_keep h hd.frame (by decide) (by decide)]; exact h216⟩⟩
  · exact Or.inr ⟨hc, hz, by omega_using [hc], m₀, q, x, hi', h208, h216⟩

theorem CI.cr {i : Nat} {s : State} (hs : CI g s₀ C D P W R L i s) : CR s₀ C D P W R L i s :=
  let ⟨_, _, _, _, hi, _, _⟩ := hs; hi.cr

theorem loop_rel (v : Ctr32Impl) (K : CCalls v g) {s₀' : State} (h : Env g s₀ C D P W R L) (h' : Env g s₀' C D P W R L)
    (hq : s₀.gpr .rsp = s₀'.gpr .rsp) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) (hPw' : (⟨P, L⟩ : Region) ∈ s₀'.wr) (n : Nat) :
    RelCT isa (fun a b => ∃ i, n = L - 16 * i ∧ CI g s₀ C D P W R L i a ∧ CI g s₀' C D P W R L i b)
      (.loop (ctrBody g.x v.callee) .ne) fun a b => CEnd s₀ C D P W R L a ∧ CEnd s₀' C D P W R L b := by
  refine RelCT.loop (M := isa) (fun (k : Nat) (a b : State) => ∃ i, k = L - 16 * i ∧ CI g s₀ C D P W R L i a ∧
    CI g s₀' C D P W R L i b) (fun k => ?_) n
  refine RelCT.exists_ fun i => ?_
  by_cases hk : k = L - 16 * i
  swap
  · exact RelCT.of_false fun a b hab => hk hab.1
  refine (((body_rel v K h h' hq i).mono (fun a b hab => ⟨hab.2.1.cr, hab.2.2.cr⟩) fun _ _ h => h).wp
    (F₁ := BPost g s₀ C D P W R L i) (F₂ := BPost g s₀' C D P W R L i)
    fun a b hab => ⟨body_wp v K h hcp hPw hab.2.1, body_wp v K h' hcp hPw' hab.2.2⟩).mono
    (fun _ _ h => h) fun a b ⟨_, ha, hb⟩ => ?_
  rcases ha with ⟨hc, hz, he⟩ | ⟨hc, hz, hci⟩ <;> rcases hb with ⟨hc', hz', he'⟩ | ⟨hc', hz', hci'⟩
  · exact ⟨by simp [eval, hz, hz'], fun _ => ⟨he, he'⟩, fun e => by simp [eval, hz] at e⟩
  · omega
  · omega
  · exact ⟨by simp [eval, hz, hz'], fun e => by simp [eval, hz] at e, fun _ =>
      ⟨L - 16 * (i + 1), by omega_using [hk, hc], i + 1, rfl, hci, hci'⟩⟩

/-- What `ctr` needs of a run: the registers, the counter `Q` (whose last
32 bits are below `2³¹`), and the slots of the data and its length. -/
structure CtrPre (s₀ : State) (C D P W : Addr) (R L : Nat) (s : State) : Prop where
  regs : Regs s₀ C D P W R L s
  cnt : ∃ (hi lo : BitVec 64) (q : List Byte), s.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = bswap64 hi ∧
    s.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = bswap64 lo ∧ (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes q ∧
    q.length = 16 ∧ Spec.Siv.beNat q % 2 ^ 32 < 2 ^ 31
  d208 : s.mem.readW (W + BitVec.ofNat 64 dataOff) 64 = P
  d216 : s.mem.readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L

/-! ## The whole blocks -/

/-- `wholePre` leaves the arguments of `vg_aes_ctr32` and the registers. -/
theorem wholePre_wp (h : Env g s₀ C D P W R L) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {s : State} (hr : Regs s₀ C D P W R L s) :
    WP isa (.block (wholePre g.x)) s fun t => WA g t (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96) P
      W R (wholeOf L) ∧ Regs s₀ C D P W R L t := by
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, r9₁, hr₁, _⟩ := wholePre_ok h hr
  exact WP.of_runBlock ⟨s₁, run₁,
    wargs h hcp hPw hr₁.rd hr₁.wr hr₁.rsp (wholeOf_le L) rdi₁ rsi₁ rdx₁ rcx₁ r8₁ r9₁, hr₁⟩

/-- `ctrWhole` is constant time: the arguments of its call, `k` blocks
among them, depend only on the registers that hold the arguments. -/
theorem whole_rel (v : Ctr32Impl) (K : CCalls v g) {s₀' : State} (h : Env g s₀ C D P W R L) (h' : Env g s₀' C D P W R L)
    (hq : s₀.gpr .rsp = s₀'.gpr .rsp) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) (hPw' : (⟨P, L⟩ : Region) ∈ s₀'.wr) :
    RelCT isa (fun a b => Regs s₀ C D P W R L a ∧ Regs s₀' C D P W R L b) (ctrWhole g.x v.callee)
      fun _ _ => True := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp]) (.block (wholePre g.x))
      hc).isSome = true := by rcases h.lay with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp]) (.block wholePost)
      hc).isSome = true := ⟨_, by taint_decide⟩
  have r₁ := (RelCT.taint (A := taint) (P := fun a b => Regs s₀ C D P W R L a ∧ Regs s₀' C D P W R L b) _
    (fun a b hab => regs_agree hq hab.1 hab.2) hA).wp
    (F₁ := fun (t : State) => WA g t (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96) P
      W R (wholeOf L) ∧ Regs s₀ C D P W R L t)
    (F₂ := fun (t : State) => WA g t (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96) P
      W R (wholeOf L) ∧ Regs s₀' C D P W R L t)
    fun a b hab => ⟨wholePre_wp h hcp hPw hab.1, wholePre_wp h' hcp hPw' hab.2⟩
  have r₂ := (K.wholeRel (P := fun (a b : State) =>
      (WA g a (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96) P W R (wholeOf L) ∧
        Regs s₀ C D P W R L a) ∧
      WA g b (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96) P W R (wholeOf L) ∧
        Regs s₀' C D P W R L b)
    fun a b hab => ⟨_, _, _, _, _, _, hab.1.1, hab.2.1, by rw [hab.1.2.rsp, hab.2.2.rsp, hq]⟩).wp
    (F₁ := Regs s₀ C D P W R L) (F₂ := Regs s₀' C D P W R L)
    fun a b hab => ⟨WP.mono (K.whole hab.1.1) fun _ p => hab.1.2.keep p.saved p.rd p.wr,
      WP.mono (K.whole hab.2.1) fun _ p => hab.2.2.keep p.saved p.rd p.wr⟩
  have r₃ := RelCT.taint (A := taint) (P := fun a b => Regs s₀ C D P W R L a ∧ Regs s₀' C D P W R L b) _
    (fun a b hab => regs_agree hq hab.1 hab.2) hB
  exact (r₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((r₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq r₃)

/-- After `ctrWhole`: block `wholeOf L` of the rest of a run, with ZF set when
no data is left. -/
def WI (g : Lay) (s₀ : State) (C D P W : Addr) (R L : Nat) (s : State) : Prop :=
  s.zf = some (decide (L - 16 * wholeOf L = 0)) ∧ ∃ m₀ q x, CInv g s₀ C D P W R L m₀ q x (wholeOf L) s ∧
    m₀.readW (W + BitVec.ofNat 64 dataOff) 64 = P ∧ m₀.readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L

theorem whole_wp (v : Ctr32Impl) (K : CCalls v g) (h : Env g s₀ C D P W R L) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {s : State} (hs : CtrPre s₀ C D P W R L s) :
    WP isa (ctrWhole g.x v.callee) s (WI g s₀ C D P W R L) := by
  obtain ⟨hi, lo, q, hhi, hlo, hq, hql, hlow⟩ := hs.cnt
  exact WP.mono (ctrWhole_wp v K h hcp hPw hs.regs hql hlow ⟨hi, lo, hhi, hlo, hq⟩) fun _ ⟨hz, hc⟩ =>
    ⟨hz, _, _, _, hc, hs.d208, hs.d216⟩

theorem WI.cend (h : Env g s₀ C D P W R L) {s : State} (hs : WI g s₀ C D P W R L s) : CEnd s₀ C D P W R L s := by
  obtain ⟨_, _, _, _, hi, h208, h216⟩ := hs
  exact ⟨hi.rbx, hi.rbp, hi.r12, hi.r15, hi.rsp, hi.rd, hi.wr,
    by rw [slot_keep h hi.frame (by decide) (by decide)]; exact h208,
    by rw [slot_keep h hi.frame (by decide) (by decide)]; exact h216⟩

theorem WI.ci {s : State} (hs : WI g s₀ C D P W R L s) (hL : 16 * wholeOf L < L) :
    CI g s₀ C D P W R L (wholeOf L) s :=
  let ⟨_, m₀, q, x, hi, h208, h216⟩ := hs; ⟨hL, m₀, q, x, hi, h208, h216⟩

theorem ctr_rel' (v : Ctr32Impl) (K : CCalls v g) {s₀' : State} (h : Env g s₀ C D P W R L) (h' : Env g s₀' C D P W R L)
    (hq : s₀.gpr .rsp = s₀'.gpr .rsp) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) (hPw' : (⟨P, L⟩ : Region) ∈ s₀'.wr) :
    RelCT isa (fun a b => CtrPre s₀ C D P W R L a ∧ CtrPre s₀' C D P W R L b) (ctr g.x v.callee)
      fun a b => Regs s₀ C D P W R L a ∧ Regs s₀' C D P W R L b := by
  have hk := wholeOf_le L
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.r15])
      (.block [.mov .r13 (.mem (at_ .r15 dataOff)), .mov .r14 (.mem (at_ .r15 lenOff))]) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have w := ((whole_rel v K h h' hq hcp hPw hPw').mono (P' := fun a b => CtrPre s₀ C D P W R L a ∧
      CtrPre s₀' C D P W R L b) (fun _ _ p => ⟨p.1.regs, p.2.regs⟩) fun _ _ p => p).wp
    (F₁ := WI g s₀ C D P W R L) (F₂ := WI g s₀' C D P W R L) fun a b hab =>
      ⟨whole_wp v K h hcp hPw hab.1, whole_wp v K h' hcp hPw' hab.2⟩
  have i := RelCT.ite (M := isa) (c := .e)
    (P := fun a b => WI g s₀ C D P W R L a ∧ WI g s₀' C D P W R L b)
    (Q := fun a b => CEnd s₀ C D P W R L a ∧ CEnd s₀' C D P W R L b)
    (fun a b hab => by show a.zf = b.zf; rw [hab.1.1, hab.2.1])
    (RelCT.block_nil fun a b hab => ⟨hab.1.1.cend h, hab.1.2.cend h'⟩)
    ((loop_rel v K h h' hq hcp hPw hPw' (L - 16 * wholeOf L)).mono (fun a b hab => by
      have hL : 16 * wholeOf L < L := by
        have e := hab.2; rw [show isa.eval .e a = a.zf from rfl, hab.1.1.1] at e
        simp at e; omega_using [e]
      exact ⟨wholeOf L, rfl, hab.1.1.ci hL, hab.1.2.ci hL⟩) fun _ _ h => h)
  have we {σ s : State} (hσ : Env g σ C D P W R L) (hs : CEnd σ C D P W R L s) :
      WP isa (.block [.mov .r13 (.mem (at_ .r15 dataOff)), .mov .r14 (.mem (at_ .r15 lenOff))]) s
        (Regs σ C D P W R L) := by
    obtain ⟨t, run, r13, r14, g, _, rd, wr⟩ := ctrEnd_ok hσ hs.r15 hs.rd hs.wr hs.d208 hs.d216
    exact WP.of_runBlock ⟨t, run, by rw [g _ (by decide) (by decide), hs.rbx], by rw [g _ (by decide) (by decide),
      hs.rbp], by rw [g _ (by decide) (by decide), hs.r12], r13, r14, by rw [g _ (by decide) (by decide), hs.r15],
      by rw [g _ (by decide) (by decide), hs.rsp], by rw [rd, hs.rd], by rw [wr, hs.wr]⟩
  have e := (RelCT.taint (A := taint) (P := fun a b => CEnd s₀ C D P W R L a ∧ CEnd s₀' C D P W R L b) _
    (fun a b hab => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr; rw [hab.1.r15, hab.2.r15]) hB).wp
    (F₁ := Regs s₀ C D P W R L) (F₂ := Regs s₀' C D P W R L) fun a b hab => ⟨we h hab.1, we h' hab.2⟩
  exact (w.mono (fun _ _ h => h) fun _ _ h => h.2).seq (i.seq (e.mono (fun _ _ h => h) fun _ _ h => h.2))

end VG.Proof.AesSiv.X86_64

end

end

/-!
# AES-SIV on x86-64: the ends of `encrypt` and `decrypt` are constant time

Both are put together from pieces: `finish` and CTR, from the registers that
hold the arguments (`finish_rel`, `ctr_rel'`), with what correctness says
about the slots of the data and the counter; and the rest, by the taint
analysis from those registers. `decrypt` compares the IVs and masks the data
without a branch, so nothing it does depends on the result.
-/

@[expose] public section

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl)

variable {g : Lay} {s₀ : State} {C D P W : Addr} {R L : Nat}

theorem finish_spre (v : UpdateImpl) (K : Calls v g) (h : Env g s₀ C D P W R L) {s : State} (hs : SPre s₀ C D P W R L s) :
    WP isa (finish g.x v.callee v.ctr.callee v.ctr.suffix 0) s (SPre s₀ C D P W R L) := by
  refine WP.mono (finish_wp v K h hs.regs (Or.inl rfl)) fun t ht => ⟨ht.regs, ?_, ?_⟩
  · rw [ht.frame.readW (Region.contains_self _ _) (fin_dis h (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)) (by decide), hs.d208]
  · rw [ht.frame.readW (Region.contains_self _ _) (fin_dis h (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)) (by decide), hs.d216]

theorem counter_ctrPre (h : Env g s₀ C D P W R L) {s : State} (hs : SPre s₀ C D P W R L s) :
    WP isa (.block (counter 0)) s (CtrPre s₀ C D P W R L) := by
  obtain ⟨s₁, run₁, m₁, g₁, rd₁, wr₁⟩ := counter_ok h hs.regs.r15 hs.regs.rd hs.regs.wr
  have fc : Frame (cntRegions W) s.mem s₁.mem := m₁ ▸ counter_frame _ _ _ _
  obtain ⟨hi, lo, e₁, e₂, e₃⟩ := counter_cnt s.mem W
  refine WP.of_runBlock ⟨s₁, run₁, hs.regs.keep (fun r hr => g₁ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide)) rd₁ wr₁,
    ⟨hi, lo, _, by rw [m₁]; exact e₁, by rw [m₁]; exact e₂, e₃, length_counter _, counter_low _⟩, ?_, ?_⟩
  · rw [fc.readW (Region.contains_self _ _) (cnt_dis (by decide) (by decide)) (by decide), hs.d208]
  · rw [fc.readW (Region.contains_self _ _) (cnt_dis (by decide) (by decide)) (by decide), hs.d216]

/-- `encrypt`'s end, from the registers and slots in both runs. -/
theorem sealTail_rel (v : UpdateImpl) (K : Calls v g) {s₀' : State} (h : Env g s₀ C D P W R L) (h' : Env g s₀' C D P W R L)
    (q1 : s₀.gpr .rsp = s₀'.gpr .rsp) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) (hPw' : (⟨P, L⟩ : Region) ∈ s₀'.wr) :
    RelCT isa (fun a b => SPre s₀ C D P W R L a ∧ SPre s₀' C D P W R L b)
      (.seq (finish g.x v.callee v.ctr.callee v.ctr.suffix 0) (.seq (.block (counter 0)) (.seq (ctr g.x v.ctr.callee) (.block restore))))
      fun _ _ => True := by
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.block (counter 0)) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ hc, (taint.check (Taint.ofRegs [.r15]) (.block restore) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have f := ((finish_rel v K h h' q1 (Or.inl rfl)).mono (P' := fun a b => SPre s₀ C D P W R L a ∧
      SPre s₀' C D P W R L b) (fun _ _ p => ⟨p.1.regs, p.2.regs⟩) fun _ _ p => p).wp
    (F₁ := SPre s₀ C D P W R L) (F₂ := SPre s₀' C D P W R L) fun a b hab =>
      ⟨finish_spre v K h hab.1, finish_spre v K h' hab.2⟩
  have c := (RelCT.taint (A := taint) (P := fun a b => SPre s₀ C D P W R L a ∧ SPre s₀' C D P W R L b) _
    (fun a b hab => regs_agree q1 hab.1.regs hab.2.regs) hB).wp
    (F₁ := CtrPre s₀ C D P W R L) (F₂ := CtrPre s₀' C D P W R L) fun a b hab =>
      ⟨counter_ctrPre h hab.1, counter_ctrPre h' hab.2⟩
  have r := RelCT.taint (A := taint) (P := fun a b => Regs s₀ C D P W R L a ∧ Regs s₀' C D P W R L b) _
    (fun a b hab => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hab.1.r15, hab.2.r15]) hC
  exact (f.mono (fun _ _ p => p) fun _ _ p => p.2).seq ((c.mono (fun _ _ p => p) fun _ _ p => p.2).seq
    ((ctr_rel' v.ctr K.toCCalls h h' q1 hcp hPw hPw').seq r))

/-- `decrypt`'s end, from the registers and slots in both runs: it compares
the IVs and masks the data without a branch, so nothing it does depends on
the result. -/
theorem openTail_rel (v : UpdateImpl) (K : Calls v g) {s₀' : State} (h : Env g s₀ C D P W R L) (h' : Env g s₀' C D P W R L)
    (q1 : s₀.gpr .rsp = s₀'.gpr .rsp) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) (hPw' : (⟨P, L⟩ : Region) ∈ s₀'.wr) :
    RelCT isa (fun a b => SPre s₀ C D P W R L a ∧ SPre s₀' C D P W R L b)
      (.seq (.block (counter 0)) (.seq (ctr g.x v.ctr.callee) (.seq (finish g.x v.callee v.ctr.callee v.ctr.suffix tOff)
        (.seq (.block Impl.AesSiv.X86_64.compare)
          (.seq maskData (.block (([.mov .rax (.mem (at_ .r15 dbOff))] : List Instr) ++ restore)))))))
      fun _ _ => True := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.block (counter 0)) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.seq (.block Impl.AesSiv.X86_64.compare)
        (.seq maskData (.block (([.mov .rax (.mem (at_ .r15 dbOff))] : List Instr) ++ restore)))) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have c := (RelCT.taint (A := taint) (P := fun a b => SPre s₀ C D P W R L a ∧ SPre s₀' C D P W R L b) _
    (fun a b hab => regs_agree q1 hab.1.regs hab.2.regs) hA).wp
    (F₁ := CtrPre s₀ C D P W R L) (F₂ := CtrPre s₀' C D P W R L) fun a b hab =>
      ⟨counter_ctrPre h hab.1, counter_ctrPre h' hab.2⟩
  have t := RelCT.taint (A := taint) (P := RR s₀ s₀' C D P W R L) _
    (fun a b hab => regs_agree q1 hab.1 hab.2) hB
  exact (c.mono (fun _ _ p => p) fun _ _ p => p.2).seq ((ctr_rel' v.ctr K.toCCalls h h' q1 hcp hPw hPw').seq
    ((finish_rel v K h h' q1 (Or.inr rfl)).seq t))

end VG.Proof.AesSiv.X86_64

end

end

/-! ### `AesSiv.X86_64.Enc`, which only this module used -/

section

/-!
# AES-SIV on x86-64: `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt`

Both save the registers in the working space and keep the arguments in them
and in its slots (`encPre_ok`), start S2V into `D = W + g.n`, after the
working space of the layout `g` (`Lay`), with the CMAC
of the zero block (`start_wp`), absorb the components of associated data,
one per iteration (`ads_wp`), and then go on as `sealTail_wp` and
`openTail_wp` say from S2V's state. `encrypt` then copies the IV from the
working space to `siv` (`sivOut_ok`), whose address and the working space's
are still on the stack (`SivArg`); `decrypt` copies the received IV from
`siv` to the working space after S2V of the associated data (`sivIn_wp`).

The proofs are on the state whose writable regions are the data, `siv` for
`encrypt`, the first `g.n` bytes of the working space and `D` (`EPre`);
`Verified.lean` moves them to the shared contracts with the working space as
an argument, one region of `g.n + 16` bytes.
-/

@[expose] public section

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0 zero2 zero2_bytes frame_store2 mn)
open VG.Proof.CmacAes.Stream.X86_64 (toNat_ofNat toNat_add_lt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl)

/-- What `encrypt` and `decrypt` need of their arguments, on the state with
narrowed permissions: the key context `C`, the rounds `R`, the `N`
descriptors at `A`, the data `P` (`L` bytes), the working space `W`, whose
address is the stack argument, and S2V's state `D` after its first `g.n`
bytes. Each component a descriptor lists is a message as the data is
(`comps`). -/
structure EPre (g : Lay) (s₀ : State) (C A P W D : Addr) (R N L : Nat) : Prop where
  env : Env g s₀ C D P W R L
  hD : D = W + BitVec.ofNat 64 g.n
  c_d : (⟨C, 512⟩ : Region).Disjoint ⟨D, 16⟩
  cp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩
  pw : (⟨P, L⟩ : Region) ∈ s₀.wr
  dw : (⟨D, 16⟩ : Region) ∈ s₀.wr
  rdi : s₀.gpr .rdi = C
  rsi : s₀.gpr .rsi = BitVec.ofNat 64 R
  rdx : s₀.gpr .rdx = A
  rcx : s₀.gpr .rcx = BitVec.ofNat 64 N
  r8 : s₀.gpr .r8 = P
  r9 : s₀.gpr .r9 = BitVec.ofNat 64 L
  arg : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 16) 64 = W
  argIn : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsp + BitVec.ofNat 64 16) 8
  descIn : (⟨A, N * 16⟩ : Region) ∈ s₀.rd ++ s₀.wr
  desc_w : (⟨A, N * 16⟩ : Region).Disjoint ⟨W, g.n⟩
  desc_d : (⟨A, N * 16⟩ : Region).Disjoint ⟨D, 16⟩
  stk_desc : (below (s₀.gpr .rsp) 16).Disjoint ⟨A, N * 16⟩
  wA : A.toNat + N * 16 ≤ 2 ^ 64
  comps : ∀ r ∈ Sig.listed 64 s₀.mem .u8 A N, Env g s₀ C D r.base W R r.len

variable {g : Lay} {s₀ : State} {C A P W D : Addr} {R N L : Nat}

/-! ## The save -/

/-- The memory after saving the registers and the arguments in the slots. -/
def encMem (s₀ : State) (A P W : Addr) (N L : Nat) : Mem :=
  ((((Spill.saveMem s₀.mem W s₀.gpr saved).writeW (W + BitVec.ofNat 64 dataOff) P).writeW
    (W + BitVec.ofNat 64 lenOff) (BitVec.ofNat 64 L)).writeW (W + BitVec.ofNat 64 adsOff) A).writeW
    (W + BitVec.ofNat 64 leftOff) (BitVec.ofNat 64 N)

theorem encPre_ok (h : EPre g s₀ C A P W D R N L) :
    ∃ s₁, runBlock isa (encPre g.n) s₀ = some s₁ ∧ Regs s₀ C D P W R L s₁ ∧ s₁.gpr .rdi = C ∧
      s₁.gpr .rsi = BitVec.ofNat 64 R ∧ s₁.gpr .rdx = D ∧ s₁.gpr .rcx = W ∧ s₁.mem = encMem s₀ A P W N L := by
  have e := h.env
  have run₀ : runBlock isa [.mov .rax (.mem (at_ .rsp 16))] s₀ = some (s₀.setReg .rax W) := by
    simp only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, State.load64, State.ea, offset_nat,
      Option.map_some, h.argIn, ite_true, h.arg]
  have hrun := Spill.save_run .rax saved (s₀.setReg .rax W) (fun p hp => by
    rw [gpr_setReg_self, wr_setReg]; have := saved_le p hp; exact e.inW rfl (by omega_arith))
  rw [gpr_setReg_self, mem_setReg] at hrun
  have w₁ := e.inW (s := s₀) rfl (d := dataOff) (n := 8) (by decide)
  have w₂ := e.inW (s := s₀) rfl (d := lenOff) (n := 8) (by decide)
  have w₃ := e.inW (s := s₀) rfl (d := adsOff) (n := 8) (by decide)
  have w₄ := e.inW (s := s₀) rfl (d := leftOff) (n := 8) (by decide)
  refine ⟨_, by
    rw [encPre, show save .rax = Spill.saveCode .rax saved from rfl, runBlock_append, runBlock_append, run₀,
      Option.bind_some, hrun, Option.bind_some]
    simp only [reduceCtorEq, imm, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, execAlu,
      State.store64, State.ea, offset_nat, Option.map_some, Option.bind_some, gpr_setReg, gpr_arithFlags,
      mem_setReg, mem_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false, w₁, w₂, w₃, w₄]
    rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [reduceCtorEq, gpr_setReg, gpr_arithFlags, mem_setReg,
    ite_true, ite_false, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.hD, sx_ofNat h.env.lay.n_lt]
  · rfl
  · rfl
  · simp only [reduceCtorEq, encMem, saved, Spill.saveMem, gpr_setReg, ite_false]

theorem encMem_frame₀ : Frame [⟨W + BitVec.ofNat 64 16, 240⟩] s₀.mem (encMem s₀ A P W N L) :=
  ((((Spill.saveMem_frame _ _ _ _ (fun p hp => Offset.contains W (by have := saved_ge p hp; omega_arith)
    (by have := saved_le p hp; omega_arith) (by decide))).writeW (List.mem_singleton_self _) _
    (Offset.contains W (by decide) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (Offset.contains W (by decide) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (Offset.contains W (by decide) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (Offset.contains W (by decide) (by decide) (by decide))

/-- The save writes the working space past its first 16 bytes (the IV
`decrypt` is given). -/
theorem encMem_frame (hg : g.Ok) : Frame [⟨W + BitVec.ofNat 64 16, g.n - 16⟩] s₀.mem (encMem s₀ A P W N L) :=
  encMem_frame₀.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.sub W (by decide) (by have := hg.lt; omega_using [this])⟩

theorem encMem_saved : Spill.Saved (encMem s₀ A P W N L) W s₀.gpr saved :=
  ((((Spill.saveMem_saved _ _ _ _ saved_slots).writeW _ (by decide) (by decide) (by decide)).writeW _ (by decide)
    (by decide) (by decide)).writeW _ (by decide) (by decide) (by decide)).writeW _ (by decide) (by decide)
    (by decide)

theorem encMem_slots :
    (encMem s₀ A P W N L).readW (W + BitVec.ofNat 64 adsOff) 64 = A ∧
    (encMem s₀ A P W N L).readW (W + BitVec.ofNat 64 leftOff) 64 = BitVec.ofNat 64 N ∧
    (encMem s₀ A P W N L).readW (W + BitVec.ofNat 64 dataOff) 64 = P ∧
    (encMem s₀ A P W N L).readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L := by
  have sp {d e : Nat} (hd : d + 8 ≤ e ∨ e + 8 ≤ d) (hd' : d + 8 ≤ 2560) (he : e + 8 ≤ 2560) :
      Mem.Sep (W + BitVec.ofNat 64 d) (64 / 8) (W + BitVec.ofNat 64 e) (64 / 8) :=
    Offset.sep W (n := 8) (k := 8) hd (by omega_arith) (by omega_arith)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [encMem]
  · rw [Mem.readW_writeW_sep (sp (d := adsOff) (e := leftOff) (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sp (d := dataOff) (e := leftOff) (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sp (d := dataOff) (e := adsOff) (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sp (d := dataOff) (e := lenOff) (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sp (d := lenOff) (e := leftOff) (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sp (d := lenOff) (e := adsOff) (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64]

/-! ## S2V's first state -/

theorem startPre_env (h : EPre g s₀ C A P W D R N L) {s : State} (hr : Regs s₀ C D P W R L s)
    (rdx : s.gpr .rdx = D) (rcx : s.gpr .rcx = W) :
    ∃ s', runBlock isa (startPre g.x) s = some s' ∧ s'.gpr .rcx = W + BitVec.ofNat 64 16 ∧
      s'.gpr .r8 = BitVec.ofNat 64 16 ∧ s'.gpr .r9 = W + BitVec.signExtend 64 g.x ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → s'.gpr r = s.gpr r) ∧
      s'.mem = zero2 (zero2 s.mem (W + BitVec.ofNat 64 16)) D ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := h.env
  have inD (d : Nat) (hd : d + 8 ≤ 16) : InRegions s.wr (D + BitVec.ofNat 64 d) 8 := by
    rw [hr.wr]; exact ⟨⟨D, 16⟩, h.dw, Offset.contains_base _ hd (by have := e.wD; omega_arith)⟩
  refine ⟨_, by
    simp only [reduceCtorEq, startPre, zero16, zOff, imm, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, readSrc32, execAlu,
      State.store64, State.ea, State.setReg32, offset_nat, Option.bind_some, Option.map_some, gpr_setReg,
      gpr_arithFlags, mem_setReg, rd_setReg, wr_setReg, ite_true, ite_false, rcx, rdx,
      e.inW hr.wr (d := 16) (n := 8) (by decide), e.inW hr.wr (d := 24) (n := 8) (by decide), inD 0 (by decide),
      inD 8 (by decide)]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [reduceCtorEq, gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
    ite_true, ite_false, rcx, sx_ofNat (show 16 < 2 ^ 31 by decide)]
  · rfl
  · intro r h₁ h₂ h₃ h₄; simp [h₁, h₂, h₃, h₄]
  · simp only [zero2, Offset.add_add, k0]
  all_goals rfl

/-- The arguments of `vg_cmac_aes_finalize` for S2V's first state: the
context as the key, the state `D`, the zero block at `W + 16` and the
layout's scratch pointer. -/
theorem EPre.fargsD (h : EPre g s₀ C A P W D R N L) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hsp : s.gpr .rsp = s₀.gpr .rsp) (rdi : s.gpr .rdi = C) (rsi : s.gpr .rsi = BitVec.ofNat 64 R)
    (rdx : s.gpr .rdx = D) (rcx : s.gpr .rcx = W + BitVec.ofNat 64 16) (r8 : s.gpr .r8 = BitVec.ofNat 64 16)
    (r9 : s.gpr .r9 = W + BitVec.signExtend 64 g.x) :
    FA g s C D (W + BitVec.ofNat 64 16) W 16 R where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  r8 := r8
  r9 := r9
  rounds := h.env.rounds
  len := by decide
  kst := h.c_d.sub_left (Region.sub_prefix (by decide))
  ks := (h.env.c_w.sub_left (Region.sub_prefix (by decide))).sub_right h.env.sX
  pst := (h.env.d_w.sub_right (h.env.sW (by decide))).symm
  ps := h.env.dX (by decide)
  sts := h.env.d_w.sub_right h.env.sX
  stkK := by rw [hsp]; exact h.env.stk_c.sub_right (Region.sub_prefix (by decide))
  stkP := by rw [hsp]; exact h.env.stk_w.sub_right (h.env.sW (by decide))
  stkSt := by rw [hsp]; exact h.env.stk_d
  stkS := by rw [hsp]; exact h.env.stk_w.sub_right h.env.sX
  wrapK := by have := h.env.wC; omega_arith
  wrapSt := h.env.wD
  wrapP := by
    rw [toNat_add_lt W h.env.wW (by omega_using [h.env.lay.lt])]; omega_using [h.env.wW, h.env.lay.lt]
  wrapS := h.env.wrapX
  reads := by
    rw [hrd, hwr]
    refine Covers.append_left (Covers.cons (cov_base h.env.ctxIn (by simp))
        (Covers.cons (Covers.right (h.env.covW (by decide))) Covers.nil))
      (Covers.cons (Covers.right (cov_base h.dw (by simp)))
        (Covers.cons (Covers.right h.env.covX) Covers.nil))
  writes := by
    rw [hwr]
    exact Covers.cons (cov_base h.dw (by simp)) (Covers.cons h.env.covX Covers.nil)

/-- The last block of the zero block, with `K1` from memory: `K1 ⊕ 0`, and
XORing it into the zero state leaves it. -/
theorem xor_lastBlock_zeros (m : Mem) (p : Addr) (k2 : List Byte) :
    Spec.Cmac.xor (Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt m p 16) k2 (Spec.Cmac.zeros 16)) (Spec.Cmac.zeros 16) =
      Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt m p 16) k2 (Spec.Cmac.zeros 16) :=
  xor_zeros (by simp [Spec.Cmac.lastBlock, Proof.Cmac.length_zeros, Proof.Cmac.length_xor,
    Proof.Cmac.bytesAt_length])

/-- The state before the `i`-th component of associated data (and, for
`i = N`, after the last): `D` is S2V's state of the first `i`, the slots at
`W + 112` and `W + 120` hold the next descriptor's address and how many are
left, and the data's, its length's and the registers' slots are as the save
left them. -/
structure AInv (g : Lay) (s₀ : State) (C A P W D : Addr) (R N L : Nat) (i : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = C
  rbp : s.gpr .rbp = BitVec.ofNat 64 R
  r12 : s.gpr .r12 = D
  r15 : s.gpr .r15 = W
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  le : i ≤ N
  ads : s.mem.readW (W + BitVec.ofNat 64 adsOff) 64 = A + BitVec.ofNat 64 (16 * i)
  left : s.mem.readW (W + BitVec.ofNat 64 leftOff) 64 = BitVec.ofNat 64 (N - i)
  d208 : s.mem.readW (W + BitVec.ofNat 64 dataOff) 64 = P
  d216 : s.mem.readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L
  saved : Spill.Saved s.mem W s₀.gpr saved
  frame : Frame [⟨W + BitVec.ofNat 64 16, g.n - 16⟩, ⟨D, 16⟩, below (s₀.gpr .rsp) 16] s₀.mem s.mem
  acc : Spec.Aes.bytesAt s.mem D 16 =
    Spec.Siv.s2vAcc (Spec.Siv.ctxMac s₀.mem C R) ((Spec.Siv.components 64 s₀.mem A N).take i)

/-- A slot of the working space outside what S2V's start writes. -/
theorem EPre.start_dis (h : EPre g s₀ C A P W D R N L) {d : Nat} (hd : 32 ≤ d) (hd' : d + 8 ≤ 256) :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 16, 16⟩ : Region), ⟨D, 16⟩, ⟨W + BitVec.ofNat 64 256, g.xn⟩,
      below (s₀.gpr .rsp) 16], Region.Disjoint ⟨W + BitVec.ofNat 64 d, 8⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint W (by omega_arith) (by omega_arith) (by omega_arith)
  · exact (h.env.d_w.sub_right (h.env.sW (by omega_arith))).symm
  · exact h.env.dX (by omega_arith)
  · exact (h.env.stk_w.sub_right (h.env.sW (by omega_arith))).symm

/-- The save, then S2V's first state `D = AES-CMAC(K1, <zero>)` with
`vg_cmac_aes_finalize` of the zero block from a zero state. -/
theorem start_wp (v : Ctr32Impl) (K : CCalls v g) (h : EPre g s₀ C A P W D R N L) :
    WP isa (.block (encPre g.n ++ startPre g.x)) s₀ fun s =>
      FA g s C D (W + BitVec.ofNat 64 16) W 16 R ∧ s.gpr .rsp = s₀.gpr .rsp ∧
      WP isa (callFinalize v.callee v.suffix) s (AInv g s₀ C A P W D R N L 0) := by
  have e := h.env
  have hRb : 16 * (R + 1) ≤ 240 := by rcases e.rounds with h | h | h <;> omega_arith
  obtain ⟨s₁, run₁, hr₁, rdi₁, rsi₁, rdx₁, rcx₁, m₁⟩ := encPre_ok h
  obtain ⟨s₂, run₂, rcx₂, r8₂, r9₂, g₂, m₂, rd₂, wr₂⟩ := startPre_env h hr₁ rdx₁ rcx₁
  have fe : Frame [⟨W + BitVec.ofNat 64 16, g.n - 16⟩] s₀.mem s₁.mem := by rw [m₁]; exact encMem_frame e.lay
  have hr₂ : Regs s₀ C D P W R L s₂ := hr₁.keep (fun r hr => g₂ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide))
    rd₂ wr₂
  have hf := h.fargsD hr₂.rd hr₂.wr hr₂.rsp (by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), rdi₁])
    (by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), rsi₁])
    (by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), rdx₁]) rcx₂ r8₂ r9₂
  refine WP.of_runBlock ⟨s₂, by rw [runBlock_append, run₁, Option.bind_some, run₂], hf, hr₂.rsp, ?_⟩
  refine WP.mono (K.fin _ hf) fun s₃ h₃ => ?_
  have hr₃ := hr₂.keep h₃.saved h₃.rd h₃.wr
  -- What S2V's start writes.
  have fz : Frame [⟨W + BitVec.ofNat 64 16, 16⟩, ⟨D, 16⟩] s₁.mem s₂.mem := by
    rw [m₂]
    exact ((frame_store2 _ _ _).sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans
      ((frame_store2 _ _ _).sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩)
  have f₃ : Frame [⟨D, 16⟩, ⟨W + BitVec.ofNat 64 256, g.xn⟩, below (s₀.gpr .rsp) 16] s₂.mem s₃.mem := by
    rw [← hr₂.rsp]; exact h₃.frame
  have fs : Frame [⟨W + BitVec.ofNat 64 16, 16⟩, ⟨D, 16⟩, ⟨W + BitVec.ofNat 64 256, g.xn⟩, below (s₀.gpr .rsp) 16]
      s₁.mem s₃.mem := by
    refine (fz.mono fun r hr => ?_).trans (f₃.mono fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> simp
  have slot {d : Nat} (hd : 32 ≤ d) (hd' : d + 8 ≤ 256) :
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = (encMem s₀ A P W N L).readW (W + BitVec.ofNat 64 d) 64 := by
    rw [fs.readW (Region.contains_self _ _) (h.start_dis hd hd') (by decide), m₁]
  obtain ⟨sl₁, sl₂, sl₃, sl₄⟩ := encMem_slots (s₀ := s₀) (A := A) (P := P) (W := W) (N := N) (L := L)
  refine ⟨hr₃.rbx, hr₃.rbp, hr₃.r12, hr₃.r15, hr₃.rsp, hr₃.rd, hr₃.wr, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [slot (by decide) (by decide), sl₁, Nat.mul_zero, k0]
  · rw [slot (by decide) (by decide), sl₂, Nat.sub_zero]
  · rw [slot (by decide) (by decide), sl₃]
  · rw [slot (by decide) (by decide), sl₄]
  · exact (m₁ ▸ encMem_saved).frame fs fun p hp => h.start_dis (by have := saved_ge p hp; omega_arith) (by have := saved_le p hp; omega_arith)
  · refine fe.sub (fun r hr => ⟨r, by simp_all, fun _ h => h⟩) |>.trans (fs.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by have := e.lay.lt; omega_using [this])⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self, Offset.sub W (by decide) (by have := e.lay.le; omega_using [this])⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩
  · -- `CIPH(0 ⊕ (0 ⊕ K1))`, the CMAC of `<zero>`.
    have f₂ : Frame [⟨W + BitVec.ofNat 64 16, g.n - 16⟩, ⟨D, 16⟩] s₀.mem s₂.mem :=
      (fe.mono fun r hr => by simp_all).trans (fz.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by have := e.lay.lt; omega_using [this])⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)
    have ctx {d n : Nat} (hd : d + n ≤ 512) :
        Spec.Aes.bytesAt s₂.mem (C + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt s₀.mem (C + BitVec.ofNat 64 d) n :=
      bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (e.c_w.sub_left (Offset.sub_base C hd)).sub_right e.sR
        · exact h.c_d.sub_left (Offset.sub_base C hd)) (by omega_arith)
    have hz : Spec.Aes.bytesAt s₂.mem (W + BitVec.ofNat 64 16) 16 = Spec.Cmac.zeros 16 := by
      rw [← zero2_bytes s₁.mem (W + BitVec.ofNat 64 16), m₂]
      exact bytesAt_frame (frame_store2 _ _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (e.d_w.sub_right (e.sW (by decide))).symm) (by decide)
    have hd : Spec.Aes.bytesAt s₂.mem D 16 = Spec.Cmac.zeros 16 := by rw [m₂]; exact zero2_bytes _ _
    have hk1 := ctx (d := 240) (n := 16) (by decide)
    have hk2 := ctx (d := 256) (n := 16) (by decide)
    have hs := ctx (d := 0) (n := 16 * (R + 1)) (by omega_arith)
    rw [k0] at hs
    rw [List.take_zero, h₃.out, mn, hz, hd, hk1, hk2, hs, Spec.Siv.s2vAcc, List.foldl_nil, Spec.Siv.s2vStart,
      Spec.Siv.ctxMac, Spec.Siv.schedCiph, show Spec.Siv.zero = [] ++ Spec.Cmac.zeros 16 from rfl,
      Siv.macWith_split _ _ _ rfl (by decide) (Or.inl rfl), chain_blocks_nil,
      Proof.Cmac.xor_comm (Spec.Cmac.zeros 16)]
    simp only [xor_lastBlock_zeros]
    rfl

/-! ## The components of associated data -/

/-- The slice the `i`-th descriptor at `A` lists. -/
def comp (m : Mem) (A : Addr) (i : Nat) : Region :=
  ⟨m.readW (A + BitVec.ofNat 64 (16 * i)) 64, (m.readW (A + BitVec.ofNat 64 (16 * i + 8)) 64).toNat⟩

theorem listed_getElem (m : Mem) (A : Addr) {N i : Nat} (hi : i < N) :
    (Sig.listed 64 m .u8 A N)[i]'(by simp [Sig.listed, hi]) = comp m A i := by
  simp only [Sig.listed, List.getElem_map, List.getElem_range, BitVec.setWidth_eq, Elem.size, Nat.mul_one, comp,
    Offset.add_add]
  rw [Nat.mul_comm]

theorem comp_mem (m : Mem) (A : Addr) {N i : Nat} (hi : i < N) : comp m A i ∈ Sig.listed 64 m .u8 A N := by
  rw [← listed_getElem m A hi]; exact List.getElem_mem _

theorem components_take_succ (m : Mem) (A : Addr) {N i : Nat} (hi : i < N) :
    (Spec.Siv.components 64 m A N).take (i + 1) =
      (Spec.Siv.components 64 m A N).take i ++ [Spec.Aes.bytesAt m (comp m A i).base (comp m A i).len] := by
  have hl : i < (Spec.Siv.components 64 m A N).length := by simp [Spec.Siv.components, Sig.listed, hi]
  rw [List.take_add_one, List.getElem?_eq_getElem hl, Option.toList_some]
  simp only [Spec.Siv.components, List.getElem_map, listed_getElem m A hi]

theorem s2vAcc_snoc (mac : List Byte → List Byte) (xs : List (List Byte)) (x : List Byte) :
    Spec.Siv.s2vAcc mac (xs ++ [x]) = Spec.Siv.s2vStep mac (Spec.Siv.s2vAcc mac xs) x := by
  simp [Spec.Siv.s2vAcc, List.foldl_append]

/-! ## S2V over the associated data -/

theorem EPre.N_lt (h : EPre g s₀ C A P W D R N L) : N < 2 ^ 64 := by have := h.wA; omega_arith

/-- The descriptors are as on entry. -/
theorem AInv.desc (h : EPre g s₀ C A P W D R N L) {i : Nat} {s : State} (hi : AInv g s₀ C A P W D R N L i s) {d : Nat}
    (hd : d + 8 ≤ N * 16) : s.mem.readW (A + BitVec.ofNat 64 d) 64 = s₀.mem.readW (A + BitVec.ofNat 64 d) 64 :=
  hi.frame.readW (Offset.contains_base A hd (by have := h.wA; omega_arith)) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.desc_w.sub_right h.env.sR
    · exact h.desc_d
    · exact h.stk_desc.symm) (by decide)

theorem AInv.keep {i : Nat} {s s' : State} (hi : AInv g s₀ C A P W D R N L i s)
    (hg : ∀ r, r ≠ .rax → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    AInv g s₀ C A P W D R N L i s' :=
  ⟨by rw [hg _ (by decide), hi.rbx], by rw [hg _ (by decide), hi.rbp], by rw [hg _ (by decide), hi.r12],
    by rw [hg _ (by decide), hi.r15], by rw [hg _ (by decide), hi.rsp], by rw [hrd, hi.rd], by rw [hwr, hi.wr], hi.le,
    hm ▸ hi.ads, hm ▸ hi.left, hm ▸ hi.d208, hm ▸ hi.d216, hm ▸ hi.saved, hm ▸ hi.frame, hm ▸ hi.acc⟩

/-- The address of the next descriptor. -/
theorem adLoad_wp (h : EPre g s₀ C A P W D R N L) {i : Nat} {s : State} (hi : AInv g s₀ C A P W D R N L i s) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 adsOff))]) s fun s' => AInv g s₀ C A P W D R N L i s' ∧
      s'.gpr .rax = A + BitVec.ofNat 64 (16 * i) ∧ s'.mem = s.mem := by
  have rA := h.env.inRW hi.rd hi.wr (d := adsOff) (n := 8) (by decide)
  refine WP.of_runBlock ⟨s.setReg .rax (A + BitVec.ofNat 64 (16 * i)), by
    simp only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, State.load64, State.ea, offset_nat,
      Option.map_some, hi.r15, rA, ite_true, hi.ads], ?_, gpr_setReg_self _ _ _, mem_setReg _ _ _⟩
  exact hi.keep (fun r hr => gpr_setReg_of_ne _ _ hr) (mem_setReg _ _ _) (rd_setReg _ _ _) (wr_setReg _ _ _)

/-- The component's address and length from its descriptor. -/
theorem adDesc_wp (h : EPre g s₀ C A P W D R N L) {i : Nat} (hiN : i < N) {s : State}
    (hi : AInv g s₀ C A P W D R N L i s) (hrax : s.gpr .rax = A + BitVec.ofNat 64 (16 * i)) :
    WP isa (.block [.mov .r13 (.mem (at_ .rax 0)), .mov .r14 (.mem (at_ .rax 8))]) s fun s' =>
      Regs s₀ C D (comp s₀.mem A i).base W R (comp s₀.mem A i).len s' ∧ s'.mem = s.mem := by
  have c₀ : InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (16 * i)) 8 := by
    rw [hi.rd, hi.wr]; exact ⟨_, h.descIn, Offset.contains_base A (by omega_arith) (by have := h.wA; omega_arith)⟩
  have c₈ : InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (16 * i + 8)) 8 := by
    rw [hi.rd, hi.wr]; exact ⟨_, h.descIn, Offset.contains_base A (by omega_arith) (by have := h.wA; omega_arith)⟩
  have d₀ := hi.desc h (d := 16 * i) (by omega_arith)
  have d₈ := hi.desc h (d := 16 * i + 8) (by omega_arith)
  refine WP.of_runBlock ⟨_, by
    simp only [reduceCtorEq, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.load64, State.ea, offset_nat, Option.map_some, gpr_setReg, rd_setReg, wr_setReg, mem_setReg, ite_true,
      ite_false, hrax, Offset.add_add, Nat.add_zero, c₀, c₈]
    rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals try simp only [reduceCtorEq, gpr_setReg, ite_true, ite_false, hi.rbx, hi.rbp, hi.r12,
    hi.r15, hi.rsp, comp, d₀, d₈]
  · exact BitVec.eq_of_toNat_eq (by rw [toNat_ofNat (BitVec.isLt _)])
  all_goals first | rfl | exact hi.rd | exact hi.wr

/-- One component: its descriptor read (`adNext_ok`), its CMAC into the
working space (`cmacOf_wp`) and the step of S2V (`adStep_wp`). -/
theorem adBody_wp (v : UpdateImpl) (K : Calls v g) (h : EPre g s₀ C A P W D R N L) {i : Nat} (hiN : i < N) {s : State}
    (hi : AInv g s₀ C A P W D R N L i s) :
    WP isa (.seq (.block adNext) (.seq (cmacOf g.x v.callee v.ctr.callee v.ctr.suffix stOff) (.block adStep))) s
      fun s' => AInv g s₀ C A P W D R N L (i + 1) s' ∧ s'.zf = some (decide (i + 1 = N)) := by
  have e := h.env
  have hN := h.N_lt
  have hRb : 16 * (R + 1) ≤ 240 := by rcases e.rounds with h | h | h <;> omega_arith
  have hQ := h.comps _ (comp_mem s₀.mem A hiN)
  rw [show adNext = [.mov .rax (.mem (at_ .r15 adsOff))] ++
    [.mov .r13 (.mem (at_ .rax 0)), .mov .r14 (.mem (at_ .rax 8))] from rfl]
  refine WP.seq (WP.block_append (WP.mono (adLoad_wp h hi) fun s₀' ⟨hi₀, rax₀, m₀⟩ =>
    WP.mono (adDesc_wp h hiN hi₀ rax₀) fun s₁ h₁ => ?_))
  obtain ⟨hr₁, m₁'⟩ := h₁
  have m₁ : s₁.mem = s.mem := by rw [m₁', m₀]
  refine WP.seq (WP.mono (cmacOf_wp v K hQ hr₁) fun s₂ h₂ => ?_)
  have hr₂ := h₂.regs
  refine WP.mono (adStep_wp hr₂.r12 hr₂.r15 (Nat.le_of_lt e.lay.lt) (by rw [hr₂.wr]; exact h.dw) (by rw [hr₂.wr]; exact e.workIn) e.d_w e.wD
    e.wW) fun s₃ ⟨b₃, g₃, rd₃, wr₃, z₃, acc₃, ads₃, left₃, f₃⟩ => ?_
  have f₂ : Frame [⟨W + BitVec.ofNat 64 128, 32⟩, ⟨W + BitVec.ofNat 64 256, g.xn⟩, below (s₀.gpr .rsp) 16] s.mem
      s₂.mem := m₁ ▸ h₂.frame
  -- The slots outside what the CMAC writes.
  have sl₂ {d : Nat} (hd : d + 8 ≤ 128 ∨ 160 ≤ d) (hd' : d + 8 ≤ 256) :
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    f₂.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Offset.disjoint W (by omega_arith) (by omega_arith) (by omega_arith)
      · exact e.dX (by omega_arith)
      · exact (e.stk_w.sub_right (e.sW (by omega_arith))).symm) (by decide)
  -- And outside what the step writes.
  have dis₃ {d : Nat} (hd : d + 8 ≤ 112 ∨ (128 ≤ d ∧ d + 8 ≤ 224) ∨ 232 ≤ d) (hd' : d + 8 ≤ 256) :
      ∀ r ∈ [(⟨D, 16⟩ : Region), ⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 224, 8⟩],
        Region.Disjoint ⟨W + BitVec.ofNat 64 d, 8⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (e.d_w.sub_right (e.sW hd')).symm
    · exact Offset.disjoint W (by omega_arith) (by omega_arith) (by omega_arith)
    · exact Offset.disjoint W (by omega_arith) (by omega_arith) (by omega_arith)
  have sl₃ {d : Nat} (hd : (160 ≤ d ∧ d + 8 ≤ 224)) :
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := by
    rw [f₃.readW (Region.contains_self _ _) (dis₃ (by omega_arith) (by omega_arith)) (by decide), sl₂ (by omega_arith) (by omega_arith)]
  have hl₂ : s₂.mem.readW (W + BitVec.ofNat 64 leftOff) 64 = BitVec.ofNat 64 (N - i) := by
    rw [sl₂ (by decide) (by decide), hi.left]
  have one : (1 : BitVec 64) = BitVec.ofNat 64 1 := rfl
  refine ⟨⟨by rw [b₃, hr₂.rbx], ?_, ?_, ?_, ?_, by rw [rd₃, hr₂.rd], by rw [wr₃, hr₂.wr], hiN, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩, ?_⟩
  · rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.rbp]
  · rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r12]
  · rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r15]
  · rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.rsp]
  · rw [ads₃, sl₂ (by decide) (by decide), hi.ads, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      Offset.add_add, Nat.mul_succ]
  · rw [left₃, hl₂, one, Offset.ofNat_sub_ofNat (by omega_arith), Nat.sub_sub]
  · rw [sl₃ (by decide), hi.d208]
  · rw [sl₃ (by decide), hi.d216]
  · refine (hi.saved.frame f₂ fun p hp => ?_).frame f₃ fun p hp => ?_
    · have := saved_ge p hp; have := saved_le p hp
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Offset.disjoint W (by omega_arith) (by omega_arith) (by omega_arith)
      · exact e.dX (by omega_arith)
      · exact (e.stk_w.sub_right (e.sW (by omega_arith))).symm
    · have := saved_ge p hp; have := saved_le p hp
      exact dis₃ (by omega_arith) (by omega_arith)
  · refine (hi.frame.trans (f₂.sub fun r hr => ?_)).trans (f₃.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, Offset.sub W (by decide) (by have := e.lay.lt; omega_using [this])⟩
      · exact ⟨_, List.mem_cons_self, Offset.sub W (by decide) (by have := e.lay.le; omega_using [this])⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_self, Offset.sub W (by decide) (by have := e.lay.lt; omega_using [this])⟩
      · exact ⟨_, List.mem_cons_self, Offset.sub W (by decide) (by have := e.lay.lt; omega_using [this])⟩
  · -- `D = dbl(D) ⊕ CMAC(Sᵢ)`.
    have dD : Spec.Aes.bytesAt s₂.mem D 16 = Spec.Aes.bytesAt s.mem D 16 :=
      bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact e.d_w.sub_right (e.sW (by decide))
        · exact e.d_w.sub_right e.sX
        · exact e.stk_d.symm) (by decide)
    have hf3 : ∀ r ∈ [(⟨W + BitVec.ofNat 64 16, g.n - 16⟩ : Region), ⟨D, 16⟩, below (s₀.gpr .rsp) 16],
        (⟨C, 512⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact e.c_w.sub_right e.sR
      · exact h.c_d
      · exact e.stk_c.symm
    have hq3 : ∀ r ∈ [(⟨W + BitVec.ofNat 64 16, g.n - 16⟩ : Region), ⟨D, 16⟩, below (s₀.gpr .rsp) 16],
        (⟨(comp s₀.mem A i).base, (comp s₀.mem A i).len⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hQ.p_w.sub_right e.sR
      · exact hQ.d_p.symm
      · exact hQ.stk_p.symm
    have o₂ := h₂.out
    rw [m₁, ctxMac_frame hi.frame hf3 hRb, bytesAt_frame hi.frame hq3 (by have := hQ.lt; omega_arith)] at o₂
    rw [acc₃, dD, o₂, hi.acc, components_take_succ s₀.mem A hiN, s2vAcc_snoc]
    rfl
  · rw [z₃, hl₂, one, Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]
    exact congrArg some (decide_eq_decide.mpr (by omega_arith))

/-- Whether there are any components: ZF is set if not. -/
theorem adsHead_wp (h : EPre g s₀ C A P W D R N L) {s : State} (hs : AInv g s₀ C A P W D R N L 0 s) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 leftOff)), .alu .test .rax (.reg .rax)]) s fun s₁ =>
      AInv g s₀ C A P W D R N L 0 s₁ ∧ s₁.zf = some (decide (N = 0)) := by
  have hN := h.N_lt
  have rL := h.env.inRW hs.rd hs.wr (d := leftOff) (n := 8) (by decide)
  obtain ⟨s₁, run₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov .rax (.mem (at_ .r15 leftOff)),
      .alu .test .rax (.reg .rax)] s = some s₁ ∧ s₁.zf = some (decide (N = 0)) ∧
      (∀ r, r ≠ .rax → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, execAlu, State.load64, State.ea,
        offset_nat, Option.map_some, Option.bind_some, hs.r15, rL, ite_true]
      rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [zf_arithFlags]
      simp only [gpr_setReg_self]
      rw [hs.left, Nat.sub_zero, BitVec.and_self, Proof.CmacAes.Stream.X86_64.beq_zero_iff, toNat_ofNat hN]
    · intro r hr; simp [gpr_setReg, hr]
    all_goals rfl
  exact WP.of_runBlock ⟨s₁, run₁, hs.keep g₁ m₁ rd₁ wr₁, zf₁⟩

/-- S2V over all the components, if there are any. -/
theorem ads_wp (v : UpdateImpl) (K : Calls v g) (h : EPre g s₀ C A P W D R N L) {s : State} (hs : AInv g s₀ C A P W D R N L 0 s) :
    WP isa (s2vAds g.x v.callee v.ctr.callee v.ctr.suffix) s (AInv g s₀ C A P W D R N L N) := by
  refine WP.seq (WP.mono (adsHead_wp h hs) fun s₁ ⟨hs₁, zf₁⟩ => ?_)
  refine WP.ite (decide (N = 0)) zf₁ (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hN0 : N = 0 := of_decide_eq_true hb
    rw [hN0] at hs₁ ⊢; exact hs₁
  have hN0 : 0 < N := Nat.pos_of_ne_zero (of_decide_eq_false hb)
  refine WP.loop (M := isa) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ i, n = N - i ∧ i < N ∧ AInv g s₀ C A P W D R N L i t) ?_ (N - 0) s₁
    ⟨0, rfl, hN0, hs₁⟩
  rintro n t ⟨i, rfl, hiN, hi⟩
  refine WP.mono (adBody_wp v K h hiN hi) fun t' ⟨hi', hz⟩ => ?_
  by_cases he : i + 1 = N
  · exact Or.inl ⟨by simp [eval, hz, he], he ▸ hi'⟩
  · exact Or.inr ⟨by simp [eval, hz, he], N - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, hi'⟩

/-- What S2V of the associated data leaves: the registers and slots as
`sealTail_wp` and `openTail_wp` take them, the saved registers, and `D`. -/
structure SDone (g : Lay) (s₀ : State) (C A P W D : Addr) (R N L : Nat) (s : State) : Prop where
  spre : SPre s₀ C D P W R L s
  saved : Spill.Saved s.mem W s₀.gpr saved
  frame : Frame [⟨W + BitVec.ofNat 64 16, g.n - 16⟩, ⟨D, 16⟩, below (s₀.gpr .rsp) 16] s₀.mem s.mem
  acc : Spec.Aes.bytesAt s.mem D 16 =
    Spec.Siv.s2vAcc (Spec.Siv.ctxMac s₀.mem C R) (Spec.Siv.components 64 s₀.mem A N)

/-- The data and its length back in their registers. -/
theorem adsEnd_wp (h : EPre g s₀ C A P W D R N L) {s : State} (hs : AInv g s₀ C A P W D R N L N s) :
    WP isa (.block [.mov .r13 (.mem (at_ .r15 dataOff)), .mov .r14 (.mem (at_ .r15 lenOff))]) s
      (SDone g s₀ C A P W D R N L) := by
  obtain ⟨s₃, run₃, r13, r14, g₃, m₃, rd₃, wr₃⟩ := ctrEnd_ok h.env hs.r15 hs.rd hs.wr hs.d208 hs.d216
  refine WP.of_runBlock ⟨s₃, run₃, ⟨⟨?_, ?_, ?_, r13, r14, ?_, ?_, by rw [rd₃, hs.rd], by rw [wr₃, hs.wr]⟩,
    m₃ ▸ hs.d208, m₃ ▸ hs.d216⟩, m₃ ▸ hs.saved, m₃ ▸ hs.frame, ?_⟩
  · rw [g₃ _ (by decide) (by decide), hs.rbx]
  · rw [g₃ _ (by decide) (by decide), hs.rbp]
  · rw [g₃ _ (by decide) (by decide), hs.r12]
  · rw [g₃ _ (by decide) (by decide), hs.r15]
  · rw [g₃ _ (by decide) (by decide), hs.rsp]
  · have hl : (Spec.Siv.components 64 s₀.mem A N).length = N := by simp [Spec.Siv.components, Sig.listed]
    rw [m₃, hs.acc, List.take_of_length_le (Nat.le_of_eq hl)]

theorem encS2v_wp (v : UpdateImpl) (K : Calls v g) (h : EPre g s₀ C A P W D R N L) :
    WP isa (encS2v g.x g.n v.callee v.ctr.callee v.ctr.suffix) s₀ (SDone g s₀ C A P W D R N L) :=
  WP.seq (WP.mono (start_wp v.ctr K.toCCalls h) fun _ h₀ => WP.seq (WP.mono h₀.2.2 fun _ h₁ =>
    WP.seq (WP.mono (ads_wp v K h h₁) fun _ h₂ => adsEnd_wp h h₂)))

/-! ## The whole functions -/

/-- The key context, the data and the return address are outside what S2V
of the associated data writes. -/
theorem EPre.sdone_dis (h : EPre g s₀ C A P W D R N L) :
    (∀ r ∈ [(⟨W + BitVec.ofNat 64 16, g.n - 16⟩ : Region), ⟨D, 16⟩, below (s₀.gpr .rsp) 16],
      (⟨C, 512⟩ : Region).Disjoint r) ∧
    (∀ r ∈ [(⟨W + BitVec.ofNat 64 16, g.n - 16⟩ : Region), ⟨D, 16⟩, below (s₀.gpr .rsp) 16],
      (⟨P, L⟩ : Region).Disjoint r) ∧
    (∀ r ∈ [(⟨W + BitVec.ofNat 64 16, g.n - 16⟩ : Region), ⟨D, 16⟩, below (s₀.gpr .rsp) 16],
      (⟨W, 16⟩ : Region).Disjoint r) ∧
    (∀ r ∈ [(⟨W + BitVec.ofNat 64 16, g.n - 16⟩ : Region), ⟨D, 16⟩, below (s₀.gpr .rsp) 16],
      (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint r) := by
  have e := h.env
  refine ⟨fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr <;> rcases hr with rfl | rfl | rfl
  · exact e.c_w.sub_right e.sR
  · exact h.c_d
  · exact e.stk_c.symm
  · exact e.p_w.sub_right e.sR
  · exact e.d_p.symm
  · exact e.stk_p.symm
  · exact Offset.base_disjoint W (by decide) (by have := e.wW; omega_arith)
  · exact (e.d_w.sub_right e.s16).symm
  · exact (e.stk_w.sub_right e.s16).symm
  · exact e.ret_w.sub_right e.sR
  · exact e.ret_d
  · exact Offset.base_disjoint_below (s₀.gpr .rsp) (n := 16) (k := 8) (by decide)

/-- The return address is outside what the ends write. -/
theorem EPre.ret_end (h : EPre g s₀ C A P W D R N L) :
    ∀ r ∈ endRegions g W P L (s₀.gpr .rsp), (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.env.ret_p
  · exact h.env.ret_w
  · exact Offset.base_disjoint_below (s₀.gpr .rsp) (n := 16) (k := 8) (by decide)

variable {T : Addr}

/-- Disjoint ranges are separate. -/
theorem sep_of_disjoint {a b : Addr} {n k n' k' : Nat} (h : (⟨a, n'⟩ : Region).Disjoint ⟨b, k'⟩)
    (hn : n ≤ n') (hk : k ≤ k') : Mem.Sep a n b k :=
  fun x h₁ h₂ => h x (by simp only [Region.Contains]; omega_arith) (by simp only [Region.Contains]; omega_arith)

/-- The synthetic IV `T`, whose address is the stack argument before the
working space's: the 16 bytes at `T` are apart from the data, the working
space, `D`, the stack and the return address, and the two stack arguments
are apart from the data, the working space and `D`. -/
structure SivArg (g : Lay) (s₀ : State) (P W D T : Addr) (L : Nat) : Prop where
  arg : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 8) 64 = T
  argIn : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsp + BitVec.ofNat 64 8) 8
  args_p : (⟨s₀.gpr .rsp + BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨P, L⟩
  args_w : (⟨s₀.gpr .rsp + BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨W, g.n⟩
  args_d : (⟨s₀.gpr .rsp + BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨D, 16⟩
  tIn : (⟨T, 16⟩ : Region) ∈ s₀.rd ++ s₀.wr
  t_p : (⟨T, 16⟩ : Region).Disjoint ⟨P, L⟩
  t_w : (⟨T, 16⟩ : Region).Disjoint ⟨W, g.n⟩
  t_d : (⟨T, 16⟩ : Region).Disjoint ⟨D, 16⟩
  stk_t : (below (s₀.gpr .rsp) 16).Disjoint ⟨T, 16⟩
  ret_t : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨T, 16⟩
  wT : T.toNat + 16 ≤ 2 ^ 64

/-- What `encrypt` and `decrypt` write: the data, the working space, `D` and
the stack. -/
abbrev allRegions (g : Lay) (W D P : Addr) (L : Nat) (sp : Addr) : List Region :=
  [⟨P, L⟩, ⟨W, g.n⟩, ⟨D, 16⟩, below sp 16]

/-- The permissions, as a postcondition. -/
theorem WP.rdwr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.rdwr he⟩

theorem EPre.all_sub (h : EPre g s₀ C A P W D R N L) :
    (∀ r ∈ [(⟨W + BitVec.ofNat 64 16, g.n - 16⟩ : Region), ⟨D, 16⟩, below (s₀.gpr .rsp) 16],
      ∃ r' ∈ allRegions g W D P L (s₀.gpr .rsp), Region.Sub r r') ∧
    (∀ r ∈ endRegions g W P L (s₀.gpr .rsp), ∃ r' ∈ allRegions g W D P L (s₀.gpr .rsp), Region.Sub r r') := by
  refine ⟨fun r hr => ?_, fun r hr => ?_⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr <;> rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.env.sR⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
      fun _ h => h⟩
  · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
      fun _ h => h⟩

/-- `encrypt` but for the copy of the IV: the IV at `W`, the ciphertext at
`P`, and nothing written but the data, the working space, `D` and the stack. -/
theorem encryptCore_wp (v : UpdateImpl) (K : Calls v g) (h : EPre g s₀ C A P W D R N L) :
    WP isa (encryptCore g.x g.n v.callee v.ctr.callee v.ctr.suffix) s₀ fun s' => gprPreserved s₀ s' ∧
      Frame (allRegions g W D P L (s₀.gpr .rsp)) s₀.mem s'.mem ∧
      Spec.Siv.encryptWith (Spec.Siv.ctxMac s₀.mem C R) (Spec.Siv.ctxCiph s₀.mem C R)
          (Spec.Siv.components 64 s₀.mem A N) (Spec.Aes.bytesAt s₀.mem P L) =
        (Spec.Aes.bytesAt s'.mem W 16, Spec.Aes.bytesAt s'.mem P L) := by
  have e := h.env
  have hRb : 16 * (R + 1) ≤ 240 := by rcases e.rounds with h | h | h <;> omega_arith
  obtain ⟨dC, dP, -, dR⟩ := h.sdone_dis
  obtain ⟨sub₁, sub₂⟩ := h.all_sub
  refine WP.seq (WP.mono (encS2v_wp v K h) fun s hs => WP.mono (sealTail_wp v K e h.cp h.pw hs.spre hs.saved)
    fun s' ⟨g', sp', f', out'⟩ => ⟨⟨fun r hr => ?_, ?_⟩, (hs.frame.sub sub₁).trans (f'.sub sub₂), ?_⟩)
  · by_cases hsp : r = .rsp
    · subst hsp; exact sp'
    · exact g' r (saved_all r hr hsp)
  · have c := Region.contains_self (s₀.gpr .rsp) 8
    rw [f'.readW c h.ret_end (by decide), hs.frame.readW c dR (by decide)]
  · rw [ctxMac_frame hs.frame dC hRb, ctxCiph_frame hs.frame dC hRb,
      bytesAt_frame hs.frame dP (by have := e.lt; omega_arith), hs.acc] at out'
    rw [Spec.Siv.encryptWith_eq]
    exact out'

/-- The stack arguments are outside what the code writes. -/
theorem SivArg.args_dis (hT : SivArg g s₀ P W D T L) {d : Nat} (hd : 8 ≤ d)
    (hd' : d + 8 ≤ 24) : ∀ r ∈ allRegions g W D P L (s₀.gpr .rsp),
      (⟨s₀.gpr .rsp + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  have hs : Region.Sub ⟨s₀.gpr .rsp + BitVec.ofNat 64 d, 8⟩ ⟨s₀.gpr .rsp + BitVec.ofNat 64 8, 16⟩ :=
    Offset.sub _ hd (by omega_arith)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hT.args_p.sub_left hs
  · exact hT.args_w.sub_left hs
  · exact hT.args_d.sub_left hs
  · exact Offset.disjoint_below _ (by omega_arith)

/-- The stack arguments are outside what S2V writes. -/
theorem SivArg.args_dis₁ (h : EPre g s₀ C A P W D R N L) (hT : SivArg g s₀ P W D T L) {d : Nat} (hd : 8 ≤ d)
    (hd' : d + 8 ≤ 24) :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 16, g.n - 16⟩ : Region), ⟨D, 16⟩, below (s₀.gpr .rsp) 16],
      (⟨s₀.gpr .rsp + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  have hs : Region.Sub ⟨s₀.gpr .rsp + BitVec.ofNat 64 d, 8⟩ ⟨s₀.gpr .rsp + BitVec.ofNat 64 8, 16⟩ :=
    Offset.sub _ hd (by omega_arith)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hT.args_w.sub_left hs).sub_right h.env.sR
  · exact hT.args_d.sub_left hs
  · exact Offset.disjoint_below _ (by omega_arith)

/-- The IV's bytes are outside what S2V writes. -/
theorem SivArg.s2v_dis (h : EPre g s₀ C A P W D R N L) (hT : SivArg g s₀ P W D T L) :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 16, g.n - 16⟩ : Region), ⟨D, 16⟩, below (s₀.gpr .rsp) 16],
      (⟨T, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hT.t_w.sub_right h.env.sR
  · exact hT.t_d
  · exact hT.stk_t.symm

/-- The copy of the IV from the working space at `W` to `T`. -/
theorem sivOut_ok {u : State} {T W : Addr} (a8 : u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 8) 64 = T)
    (a16 : u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 16) 64 = W)
    (i8 : InRegions (u.rd ++ u.wr) (u.gpr .rsp + BitVec.ofNat 64 8) 8)
    (i16 : InRegions (u.rd ++ u.wr) (u.gpr .rsp + BitVec.ofNat 64 16) 8)
    (iW₀ : InRegions (u.rd ++ u.wr) (W + BitVec.ofNat 64 0) 8)
    (iW₈ : InRegions (u.rd ++ u.wr) (W + BitVec.ofNat 64 8) 8)
    (oT₀ : InRegions u.wr (T + BitVec.ofNat 64 0) 8) (oT₈ : InRegions u.wr (T + BitVec.ofNat 64 8) 8) :
    ∃ u', runBlock isa sivOut u = some u' ∧
      u'.mem = (u.mem.writeW (T + BitVec.ofNat 64 0) (u.mem.readW (W + BitVec.ofNat 64 0) 64)).writeW
        (T + BitVec.ofNat 64 8)
        ((u.mem.writeW (T + BitVec.ofNat 64 0) (u.mem.readW (W + BitVec.ofNat 64 0) 64)).readW
          (W + BitVec.ofNat 64 8) 64) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → u'.gpr r = u.gpr r) ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, sivOut, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.load64, State.store64, State.ea, offset_nat, Option.map_some, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, ite_true, ite_false, a8, a16, i8, i16, iW₀, iW₈, oT₀, oT₈]
    rfl, ?_, ?_, ?_, ?_⟩
  · rfl
  · intro r h₁ h₂ h₃; simp [gpr_setReg, h₁, h₂, h₃]
  all_goals rfl

/-- What the copy of the IV reads after `encryptCore`: the stack arguments. -/
structure OutPre (s₀ : State) (W T : Addr) (u : State) : Prop where
  sp : u.gpr .rsp = s₀.gpr .rsp
  a8 : u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 8) 64 = T
  a16 : u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 16) 64 = W
  i8 : InRegions (u.rd ++ u.wr) (u.gpr .rsp + BitVec.ofNat 64 8) 8
  i16 : InRegions (u.rd ++ u.wr) (u.gpr .rsp + BitVec.ofNat 64 16) 8

theorem outPre_of (h : EPre g s₀ C A P W D R N L) (hT : SivArg g s₀ P W D T L) {u : State}
    (gp : gprPreserved s₀ u) (f : Frame (allRegions g W D P L (s₀.gpr .rsp)) s₀.mem u.mem) (rd : u.rd = s₀.rd)
    (wr : u.wr = s₀.wr) : OutPre s₀ W T u := by
  have sp : u.gpr .rsp = s₀.gpr .rsp := gp.1 .rsp (by decide)
  refine ⟨sp, ?_, ?_, by rw [rd, wr, sp]; exact hT.argIn, by rw [rd, wr, sp]; exact h.argIn⟩
  · rw [sp, ← hT.arg]
    exact f.readW (Region.contains_self _ _) (hT.args_dis (d := 8) (by decide) (by decide)) (by decide)
  · rw [sp, ← h.arg]
    exact f.readW (Region.contains_self _ _) (hT.args_dis (d := 16) (by decide) (by decide)) (by decide)

/-- `encryptCore` ends where the copy of the IV can read its stack arguments. -/
theorem encryptCore_out (v : UpdateImpl) (K : Calls v g) (h : EPre g s₀ C A P W D R N L) (hT : SivArg g s₀ P W D T L) :
    WP isa (encryptCore g.x g.n v.callee v.ctr.callee v.ctr.suffix) s₀ (OutPre s₀ W T) :=
  WP.mono (WP.rdwr (encryptCore_wp v K h)) fun _ ⟨⟨gp, f, _⟩, rd, wr⟩ => outPre_of h hT gp f rd wr

/-- The first two loads of `sivOut`: the addresses of `siv` and the working space. -/
theorem sivOutHead_wp {u : State} (hu : OutPre s₀ W T u) :
    WP isa (.block (sivOut.take 2)) u fun u' => u'.gpr .rax = T ∧ u'.gpr .r10 = W :=
  WP.of_runBlock ⟨_, by
    simp only [reduceCtorEq, sivOut, List.take, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.load64, State.ea, offset_nat, Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      ite_true, ite_false, hu.i8, hu.a8, hu.i16, hu.a16]
    rfl, by simp [gpr_setReg], by simp [gpr_setReg]⟩

theorem encrypt_wp (v : UpdateImpl) (K : Calls v g) (h : EPre g s₀ C A P W D R N L) (hT : SivArg g s₀ P W D T L)
    (hTw : (⟨T, 16⟩ : Region) ∈ s₀.wr) :
    WP isa (encrypt g.x g.n v.callee v.ctr.callee v.ctr.suffix) s₀ fun s' => gprPreserved s₀ s' ∧
      Spec.Siv.encryptWith (Spec.Siv.ctxMac s₀.mem C R) (Spec.Siv.ctxCiph s₀.mem C R)
          (Spec.Siv.components 64 s₀.mem A N) (Spec.Aes.bytesAt s₀.mem P L) =
        (Spec.Aes.bytesAt s'.mem T 16, Spec.Aes.bytesAt s'.mem P L) := by
  have e := h.env
  refine WP.seq (WP.mono (WP.rdwr (encryptCore_wp v K h)) fun u ⟨⟨⟨gp, ret⟩, f, out⟩, rd, wr⟩ => ?_)
  have hu := outPre_of h hT ⟨gp, ret⟩ f rd wr
  have iW (d : Nat) (hd : d + 8 ≤ 16) : InRegions (u.rd ++ u.wr) (W + BitVec.ofNat 64 d) 8 :=
    e.inRW rd wr (by omega_arith)
  have oT (d : Nat) (hd : d + 8 ≤ 16) : InRegions u.wr (T + BitVec.ofNat 64 d) 8 := by
    rw [wr]; exact ⟨_, hTw, Offset.contains_base T hd (by have := hT.wT; omega_arith)⟩
  obtain ⟨u', run, m', g', -, -⟩ := sivOut_ok hu.a8 hu.a16 hu.i8 hu.i16 (iW 0 (by decide)) (iW 8 (by decide))
    (oT 0 (by decide)) (oT 8 (by decide))
  refine WP.of_runBlock ⟨u', run, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · rw [g' r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide)
      (by rintro rfl; revert hr; decide), gp r hr]
  · -- The return address, apart from `T`.
    have fT : Frame [⟨T, 16⟩] u.mem u'.mem := by rw [m']; exact Proof.CmacAes.X86_64.frame_store2' T _ _
    rw [fT.readW (Region.contains_self _ _) (one_out hT.ret_t) (by decide), ret]
  · have fT : Frame [⟨T, 16⟩] u.mem u'.mem := by rw [m']; exact Proof.CmacAes.X86_64.frame_store2' T _ _
    rw [out, bytesAt_frame fT (one_out hT.t_p.symm) (by have := e.lt; omega_arith)]
    have sp8 : Mem.Sep (W + BitVec.ofNat 64 8) (64 / 8) T (64 / 8) :=
      sep_of_disjoint (hT.t_w.sub_right (e.sW (d := 8) (n := 8) (by decide))).symm (by decide) (by decide)
    rw [m', k0, k0, Mem.readW_writeW_sep sp8 (by decide), Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_readW,
      Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split]

/-- The copy of the IV from `T` to the working space at `W`. -/
theorem sivIn_ok {u : State} {T W : Addr} (a8 : u.mem.readW (u.gpr .rsp + BitVec.ofNat 64 8) 64 = T)
    (r15 : u.gpr .r15 = W)
    (i8 : InRegions (u.rd ++ u.wr) (u.gpr .rsp + BitVec.ofNat 64 8) 8)
    (iT₀ : InRegions (u.rd ++ u.wr) (T + BitVec.ofNat 64 0) 8)
    (iT₈ : InRegions (u.rd ++ u.wr) (T + BitVec.ofNat 64 8) 8)
    (oW₀ : InRegions u.wr (W + BitVec.ofNat 64 0) 8) (oW₈ : InRegions u.wr (W + BitVec.ofNat 64 8) 8) :
    ∃ u', runBlock isa sivIn u = some u' ∧
      u'.mem = (u.mem.writeW (W + BitVec.ofNat 64 0) (u.mem.readW (T + BitVec.ofNat 64 0) 64)).writeW
        (W + BitVec.ofNat 64 8)
        ((u.mem.writeW (W + BitVec.ofNat 64 0) (u.mem.readW (T + BitVec.ofNat 64 0) 64)).readW
          (T + BitVec.ofNat 64 8) 64) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → u'.gpr r = u.gpr r) ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, sivIn, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.load64, State.store64, State.ea, offset_nat, Option.map_some, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, ite_true, ite_false, a8, r15, i8, iT₀, iT₈, oW₀, oW₈]
    rfl, ?_, ?_, ?_, ?_⟩
  · rfl
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  all_goals rfl

/-- The address of `siv`, on the stack, after S2V. -/
theorem SDone.argT (h : EPre g s₀ C A P W D R N L) (hT : SivArg g s₀ P W D T L) {s : State}
    (hs : SDone g s₀ C A P W D R N L s) : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 8) 64 = T := by
  rw [hs.spre.regs.rsp, ← hT.arg]
  exact hs.frame.readW (Region.contains_self _ _) (hT.args_dis₁ h (d := 8) (by decide) (by decide)) (by decide)

/-- The first load of `sivIn`: the address of `siv`. -/
theorem sivInHead_wp (h : EPre g s₀ C A P W D R N L) (hT : SivArg g s₀ P W D T L) {s : State}
    (hs : SDone g s₀ C A P W D R N L s) :
    WP isa (.block (sivIn.take 1)) s fun s' => s'.gpr .rax = T ∧ s'.gpr .r15 = W := by
  have hr := hs.spre.regs
  have i8 : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8 := by
    rw [hr.rd, hr.wr, hr.rsp]; exact hT.argIn
  exact WP.of_runBlock ⟨_, by
    simp only [sivIn, List.take, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.load64, State.ea, offset_nat, Option.map_some, ite_true, i8, hs.argT h hT]
    rfl, by simp [gpr_setReg], by simp [gpr_setReg, hr.r15]⟩

/-- What `sivIn` keeps of S2V's end, with the received IV now at `W`. -/
theorem sivIn_wp (h : EPre g s₀ C A P W D R N L) (hT : SivArg g s₀ P W D T L) {s : State}
    (hs : SDone g s₀ C A P W D R N L s) :
    WP isa (.block sivIn) s fun s' => SPre s₀ C D P W R L s' ∧ Spill.Saved s'.mem W s₀.gpr saved ∧
      Frame [⟨W, 16⟩] s.mem s'.mem ∧ Spec.Aes.bytesAt s'.mem W 16 = Spec.Aes.bytesAt s₀.mem T 16 := by
  have e := h.env
  have hr := hs.spre.regs
  have a8 := hs.argT h hT
  have i8 : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8 := by
    rw [hr.rd, hr.wr, hr.rsp]; exact hT.argIn
  have iT (d : Nat) (hd : d + 8 ≤ 16) : InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 d) 8 := by
    rw [hr.rd, hr.wr]; exact ⟨_, hT.tIn, Offset.contains_base T hd (by have := hT.wT; omega_arith)⟩
  obtain ⟨s', run, m', g', rd', wr'⟩ := sivIn_ok a8 hr.r15 i8 (iT 0 (by decide)) (iT 8 (by decide))
    (e.inW hr.wr (d := 0) (by decide)) (e.inW hr.wr (d := 8) (by decide))
  have fW : Frame [⟨W, 16⟩] s.mem s'.mem := by rw [m']; exact Proof.CmacAes.X86_64.frame_store2' W _ _
  have slot {d : Nat} (hd : 16 ≤ d) (hd' : d + 8 ≤ 2560) :
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fW.readW (Region.contains_self _ _) (one_out (Offset.disjoint_base W (by omega_arith) (by have := e.wW; omega_arith)))
      (by decide)
  refine WP.of_runBlock ⟨s', run, ⟨hr.keep (fun r hr' => g' r (by rintro rfl; revert hr'; decide)
      (by rintro rfl; revert hr'; decide)) rd' wr', by rw [slot (by decide) (by decide), hs.spre.d208],
      by rw [slot (by decide) (by decide), hs.spre.d216]⟩, hs.saved.frame fW fun p hp => one_out
        (Offset.disjoint_base W (by have := saved_ge p hp; omega_arith) (by have := saved_le p hp; have := e.wW; omega_arith)),
    fW, ?_⟩
  have sp8 : Mem.Sep (T + BitVec.ofNat 64 8) (64 / 8) W (64 / 8) :=
    sep_of_disjoint ((hT.t_w.sub_left (Offset.sub_base T (d := 8) (n := 8) (by decide))).sub_right
      e.s16) (by decide) (by decide)
  rw [m', k0, k0, Mem.readW_writeW_sep sp8 (by decide), Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_readW,
    Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split]
  exact bytesAt_frame hs.frame (hT.s2v_dis h) (by decide)

theorem decrypt_wp (v : UpdateImpl) (K : Calls v g) (h : EPre g s₀ C A P W D R N L) (hT : SivArg g s₀ P W D T L) :
    WP isa (decrypt g.x g.n v.callee v.ctr.callee v.ctr.suffix) s₀ fun s' => gprPreserved s₀ s' ∧
      match Spec.Siv.decryptWith (Spec.Siv.ctxMac s₀.mem C R) (Spec.Siv.ctxCiph s₀.mem C R)
          (Spec.Siv.components 64 s₀.mem A N) (Spec.Aes.bytesAt s₀.mem T 16) (Spec.Aes.bytesAt s₀.mem P L) with
      | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ Spec.Aes.bytesAt s'.mem P L = pt
      | none => (s'.gpr .rax).setWidth 32 = 0 ∧ Spec.Aes.bytesAt s'.mem P L = Spec.Siv.zeros L := by
  have e := h.env
  have hRb : 16 * (R + 1) ≤ 240 := by rcases e.rounds with h | h | h <;> omega_arith
  obtain ⟨dC, dP, -, dR⟩ := h.sdone_dis
  have wC := one_out (e.c_w.sub_right e.s16)
  refine WP.seq (WP.mono (encS2v_wp v K h) fun s hs => WP.seq (WP.mono (sivIn_wp h hT hs)
    fun s₁ ⟨sp₁, sv₁, f₁, v₁⟩ => WP.mono (openTail_wp v K e h.cp h.pw sp₁ sv₁)
    fun s' ⟨g', sp', f', out'⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩))
  · by_cases hsp : r = .rsp
    · subst hsp; exact sp'
    · exact g' r (saved_all r hr hsp)
  · have c := Region.contains_self (s₀.gpr .rsp) 8
    rw [f'.readW c h.ret_end (by decide),
      f₁.readW c (one_out (e.ret_w.sub_right e.s16)) (by decide),
      hs.frame.readW c dR (by decide)]
  · rw [ctxMac_frame f₁ wC hRb, ctxCiph_frame f₁ wC hRb,
      bytesAt_frame f₁ (one_out (e.p_w.symm.sub_left e.s16).symm) (by have := e.lt; omega_arith),
      bytesAt_frame f₁ (one_out (e.d_w.sub_right e.s16)) (by decide), v₁,
      ctxMac_frame hs.frame dC hRb, ctxCiph_frame hs.frame dC hRb,
      bytesAt_frame hs.frame dP (by have := e.lt; omega_arith), hs.acc] at out'
    rw [Spec.Siv.decryptWith_eq]
    exact out'

end VG.Proof.AesSiv.X86_64

end

end

/-!
# AES-SIV on x86-64: `encrypt` and `decrypt` are constant time

Two runs with the same public arguments and the same descriptors (`EPub`)
leak the same trace. The taint analysis proves the straight-line pieces from
the registers that are public, with what correctness says about the values
they load: the working space's address from the stack (`argLoad_wp`), and in
each iteration the next descriptor's address from its slot and the
component's address and length from the descriptor (`adLoad_wp`,
`adDesc_wp`), the same in both runs since the descriptors are. The calls are
related by their callees' contracts (`fin_rel`, `cmacOf_rel`), and the end by
`sealTail_rel` and `openTail_rel`.
-/

@[expose] public section

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl)

variable {g : Lay} {s₀ s₀' : State} {C A P W D : Addr} {R N L : Nat}

/-- What two runs agree on besides the arguments `EPre` names: the stack
pointer and the descriptors. -/
structure EPub (s₀ s₀' : State) (A : Addr) (N : Nat) : Prop where
  rsp : s₀.gpr .rsp = s₀'.gpr .rsp
  desc : ∀ j < N * 16, s₀.mem (A + BitVec.ofNat 64 j) = s₀'.mem (A + BitVec.ofNat 64 j)

/-- The same descriptors list the same components. -/
theorem EPub.comp_eq (hq : EPub s₀ s₀' A N) {i : Nat} (hi : i < N) : comp s₀.mem A i = comp s₀'.mem A i := by
  have r {d : Nat} (hd : d + 8 ≤ N * 16) : s₀.mem.readW (A + BitVec.ofNat 64 d) 64 =
      s₀'.mem.readW (A + BitVec.ofNat 64 d) 64 := by
    have e := Mem.read_congr (m := s₀.mem) (m' := s₀'.mem) (a := A + BitVec.ofNat 64 d) (n := 64 / 8)
      fun j hj => by rw [Offset.add_add]; exact hq.desc (d + j) (by omega_using [hd, hj])
    simp only [Mem.readW, e]
  unfold comp
  rw [r (d := 16 * i) (by omega_using [hi]), r (d := 16 * i + 8) (by omega_using [hi])]

/-- The working space's address, from the stack. -/
theorem argLoad_wp (h : EPre g s₀ C A P W D R N L) :
    WP isa (.block [.mov .rax (.mem (at_ .rsp 16))]) s₀ fun s =>
      s.gpr .rax = W ∧ ∀ r, r ≠ .rax → s.gpr r = s₀.gpr r :=
  WP.of_runBlock ⟨s₀.setReg .rax W, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, State.load64, State.ea, offset_nat,
      Option.map_some, h.argIn, ite_true, h.arg], gpr_setReg_self _ _ _, fun r hr => gpr_setReg_of_ne _ _ hr⟩

/-- The arguments in both runs. -/
theorem args_agree (h : EPre g s₀ C A P W D R N L) (h' : EPre g s₀' C A P W D R N L) (q1 : s₀.gpr .rsp = s₀'.gpr .rsp)
    {a b : State} (ha : a.gpr .rax = W ∧ ∀ r, r ≠ .rax → a.gpr r = s₀.gpr r)
    (hb : b.gpr .rax = W ∧ ∀ r, r ≠ .rax → b.gpr r = s₀'.gpr r) :
    taint.Agree (Taint.ofRegs [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) a b := by
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ha.1, hb.1]
  · rw [ha.2 _ (by decide), hb.2 _ (by decide), h.rdi, h'.rdi]
  · rw [ha.2 _ (by decide), hb.2 _ (by decide), h.rsi, h'.rsi]
  · rw [ha.2 _ (by decide), hb.2 _ (by decide), h.rdx, h'.rdx]
  · rw [ha.2 _ (by decide), hb.2 _ (by decide), h.rcx, h'.rcx]
  · rw [ha.2 _ (by decide), hb.2 _ (by decide), h.r8, h'.r8]
  · rw [ha.2 _ (by decide), hb.2 _ (by decide), h.r9, h'.r9]
  · rw [ha.2 _ (by decide), hb.2 _ (by decide), q1]

/-- The state before the components, in both runs. -/
abbrev AA (g : Lay) (s₀ s₀' : State) (C A P W D : Addr) (R N L i : Nat) (a b : State) : Prop :=
  AInv g s₀ C A P W D R N L i a ∧ AInv g s₀' C A P W D R N L i b

/-- The registers the taint analysis needs public in the loop. -/
theorem ainv_agree (q1 : s₀.gpr .rsp = s₀'.gpr .rsp) {i : Nat} {a b : State} (hab : AA g s₀ s₀' C A P W D R N L i a b) :
    taint.Agree (Taint.ofRegs [.rbx, .rbp, .r12, .r15, .rsp]) a b := by
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [hab.1.rbx, hab.2.rbx]
  · rw [hab.1.rbp, hab.2.rbp]
  · rw [hab.1.r12, hab.2.r12]
  · rw [hab.1.r15, hab.2.r15]
  · rw [hab.1.rsp, hab.2.rsp, q1]

/-- The save and S2V's first state. -/
theorem start_rel (v : Ctr32Impl) (K : CCalls v g) (h : EPre g s₀ C A P W D R N L) (h' : EPre g s₀' C A P W D R N L)
    (q1 : s₀.gpr .rsp = s₀'.gpr .rsp) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀')
      (.seq (.block (encPre g.n ++ startPre g.x)) (callFinalize v.callee v.suffix))
      (AA g s₀ s₀' C A P W D R N L 0) := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
      (.block [.mov .rax (.mem (at_ .rsp 16))]) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
      (.block ((encPre g.n).drop 1 ++ startPre g.x)) hc).isSome = true := by
    rcases h.env.lay with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _ (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h.rdi, h'.rdi]
    · rw [h.rsi, h'.rsi]
    · rw [h.rdx, h'.rdx]
    · rw [h.rcx, h'.rcx]
    · rw [h.r8, h'.r8]
    · rw [h.r9, h'.r9]
    · exact q1) hA).wp
    (F₁ := fun (s : State) => s.gpr .rax = W ∧ ∀ r, r ≠ .rax → s.gpr r = s₀.gpr r)
    (F₂ := fun (s : State) => s.gpr .rax = W ∧ ∀ r, r ≠ .rax → s.gpr r = s₀'.gpr r) fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab; exact ⟨argLoad_wp h, argLoad_wp h'⟩
  have b := RelCT.taint (A := taint) (P := fun (a b : State) => (a.gpr .rax = W ∧ ∀ r, r ≠ .rax → a.gpr r = s₀.gpr r) ∧
      b.gpr .rax = W ∧ ∀ r, r ≠ .rax → b.gpr r = s₀'.gpr r) _ (fun a b hab => args_agree h h' q1 hab.1 hab.2) hB
  have blk := (RelCT.block_append (M := isa) (l₁ := ([.mov .rax (.mem (at_ .rsp 16))] : List Instr)) (l₂ := (encPre g.n).drop 1 ++ startPre g.x)
      ((a.mono (fun _ _ p => p) fun _ _ p => p.2).seq b)).wp
    (F₁ := fun (s : State) => FA g s C D (W + BitVec.ofNat 64 16) W 16 R ∧
      s.gpr .rsp = s₀.gpr .rsp ∧ WP isa (callFinalize v.callee v.suffix) s (AInv g s₀ C A P W D R N L 0))
    (F₂ := fun (s : State) => FA g s C D (W + BitVec.ofNat 64 16) W 16 R ∧
      s.gpr .rsp = s₀'.gpr .rsp ∧ WP isa (callFinalize v.callee v.suffix) s (AInv g s₀' C A P W D R N L 0))
    fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨start_wp v K h, start_wp v K h'⟩
  have f := (K.finRel ("vg_cmac_aes_finalize" ++ v.suffix)
    (P := fun a b => (FA g a C D (W + BitVec.ofNat 64 16) W 16 R ∧
      a.gpr .rsp = s₀.gpr .rsp ∧ WP isa (callFinalize v.callee v.suffix) a (AInv g s₀ C A P W D R N L 0)) ∧
      FA g b C D (W + BitVec.ofNat 64 16) W 16 R ∧
      b.gpr .rsp = s₀'.gpr .rsp ∧ WP isa (callFinalize v.callee v.suffix) b (AInv g s₀' C A P W D R N L 0))
    fun a b hab => ⟨_, _, _, _, _, _, hab.1.1, hab.2.1, by rw [hab.1.2.1, hab.2.2.1, q1]⟩).wp
    (F₁ := AInv g s₀ C A P W D R N L 0) (F₂ := AInv g s₀' C A P W D R N L 0)
    fun a b hab => ⟨by exact hab.1.2.2, by exact hab.2.2.2⟩
  exact (blk.mono (fun _ _ p => p) fun _ _ p => p.2).seq (f.mono (fun _ _ p => p) fun _ _ p => p.2)

/-- One component in both runs. -/
theorem adBody_rel (v : UpdateImpl) (K : Calls v g) (h : EPre g s₀ C A P W D R N L) (h' : EPre g s₀' C A P W D R N L)
    (hq : EPub s₀ s₀' A N) {i : Nat} (hiN : i < N) :
    RelCT isa (AA g s₀ s₀' C A P W D R N L i)
      (.seq (.block adNext) (.seq (cmacOf g.x v.callee v.ctr.callee v.ctr.suffix stOff) (.block adStep)))
      fun a b => (AInv g s₀ C A P W D R N L (i + 1) a ∧ a.zf = some (decide (i + 1 = N))) ∧
        AInv g s₀' C A P W D R N L (i + 1) b ∧ b.zf = some (decide (i + 1 = N)) := by
  have hQ := h.comps _ (comp_mem s₀.mem A hiN)
  have hQ' := h'.comps _ (comp_mem s₀'.mem A hiN)
  have ec := hq.comp_eq hiN
  rw [← ec] at hQ'
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r15, .rsp])
      (.block [.mov .rax (.mem (at_ .r15 adsOff))]) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rax, .rbx, .rbp, .r12, .r15, .rsp])
      (.block [.mov .r13 (.mem (at_ .rax 0)), .mov .r14 (.mem (at_ .rax 8))]) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.block adStep) hc).isSome = true := ⟨_, by taint_decide⟩
  have p₁ := (RelCT.taint (A := taint) (P := AA g s₀ s₀' C A P W D R N L i) _
    (fun a b hab => ainv_agree hq.rsp hab) hA).wp
    (F₁ := fun (s : State) => AInv g s₀ C A P W D R N L i s ∧ s.gpr .rax = A + BitVec.ofNat 64 (16 * i))
    (F₂ := fun (s : State) => AInv g s₀' C A P W D R N L i s ∧ s.gpr .rax = A + BitVec.ofNat 64 (16 * i))
    fun a b hab => ⟨WP.mono (adLoad_wp h hab.1) fun _ p => ⟨p.1, p.2.1⟩,
      WP.mono (adLoad_wp h' hab.2) fun _ p => ⟨p.1, p.2.1⟩⟩
  have p₂ := (RelCT.taint (A := taint)
    (P := fun (a b : State) => (AInv g s₀ C A P W D R N L i a ∧ a.gpr .rax = A + BitVec.ofNat 64 (16 * i)) ∧
      AInv g s₀' C A P W D R N L i b ∧ b.gpr .rax = A + BitVec.ofNat 64 (16 * i)) _
    (fun a b hab => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hab.1.2, hab.2.2]
      · rw [hab.1.1.rbx, hab.2.1.rbx]
      · rw [hab.1.1.rbp, hab.2.1.rbp]
      · rw [hab.1.1.r12, hab.2.1.r12]
      · rw [hab.1.1.r15, hab.2.1.r15]
      · rw [hab.1.1.rsp, hab.2.1.rsp, hq.rsp]) hB).wp
    (F₁ := Regs s₀ C D (comp s₀.mem A i).base W R (comp s₀.mem A i).len)
    (F₂ := Regs s₀' C D (comp s₀.mem A i).base W R (comp s₀.mem A i).len)
    fun a b hab => ⟨WP.mono (adDesc_wp h hiN hab.1.1 hab.1.2) fun _ p => p.1,
      WP.mono (adDesc_wp h' hiN hab.2.1 hab.2.2) fun _ p => by rw [ec]; exact p.1⟩
  have p₄ := RelCT.taint (A := taint)
    (P := RR s₀ s₀' C D (comp s₀.mem A i).base W R (comp s₀.mem A i).len) _
    (fun a b hab => regs_agree hq.rsp hab.1 hab.2) hC
  have body := (RelCT.block_append (M := isa) ((p₁.mono (fun _ _ p => p) fun _ _ p => p.2).seq
    (p₂.mono (fun _ _ p => p) fun _ _ p => p.2))).seq ((cmacOf_rel v K hQ hQ' hq.rsp).seq p₄)
  refine (body.wp (F₁ := fun (s : State) => AInv g s₀ C A P W D R N L (i + 1) s ∧ s.zf = some (decide (i + 1 = N)))
    (F₂ := fun (s : State) => AInv g s₀' C A P W D R N L (i + 1) s ∧ s.zf = some (decide (i + 1 = N)))
    fun a b hab => ⟨by exact adBody_wp v K h hiN hab.1, by exact adBody_wp v K h' hiN hab.2⟩).mono
    (fun _ _ p => p) fun _ _ p => p.2

/-- S2V over the components in both runs. -/
theorem ads_rel (v : UpdateImpl) (K : Calls v g) (h : EPre g s₀ C A P W D R N L) (h' : EPre g s₀' C A P W D R N L)
    (hq : EPub s₀ s₀' A N) :
    RelCT isa (AA g s₀ s₀' C A P W D R N L 0) (s2vAds g.x v.callee v.ctr.callee v.ctr.suffix) (AA g s₀ s₀' C A P W D R N L N) := by
  obtain ⟨_, hH⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r15, .rsp])
      (.block [.mov .rax (.mem (at_ .r15 leftOff)), .alu .test .rax (.reg .rax)]) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have hd := (RelCT.taint (A := taint) (P := AA g s₀ s₀' C A P W D R N L 0) _
    (fun a b hab => ainv_agree hq.rsp hab) hH).wp
    (F₁ := fun (s : State) => AInv g s₀ C A P W D R N L 0 s ∧ s.zf = some (decide (N = 0)))
    (F₂ := fun (s : State) => AInv g s₀' C A P W D R N L 0 s ∧ s.zf = some (decide (N = 0)))
    fun a b hab => ⟨adsHead_wp h hab.1, adsHead_wp h' hab.2⟩
  refine (hd.mono (fun _ _ p => p) fun _ _ p => p.2).seq (RelCT.ite (fun a b hab => by
    show a.zf = b.zf; rw [hab.1.2, hab.2.2]) ?_ ?_)
  · refine RelCT.block_nil fun a b hab => ?_
    have e := hab.2
    rw [show isa.eval .e a = a.zf from rfl, hab.1.1.2] at e
    have hN0 : N = 0 := by simpa using e
    rw [hN0] at hab ⊢
    exact ⟨hab.1.1.1, hab.1.2.1⟩
  by_cases hN0 : N = 0
  · exact RelCT.of_false fun a b hab => by
      have e := hab.2; rw [show isa.eval .e a = a.zf from rfl, hab.1.1.2] at e; simp [hN0] at e
  refine (RelCT.loop (M := isa) (c := .ne)
    (fun (n : Nat) (a b : State) => ∃ i, n = N - i ∧ i < N ∧ AA g s₀ s₀' C A P W D R N L i a b) (fun n => ?_)
    (N - 0)).mono (fun a b hab => ⟨0, rfl, Nat.pos_of_ne_zero hN0, hab.1.1.1, hab.1.2.1⟩) fun _ _ p => p
  refine RelCT.exists_ fun i => ?_
  by_cases hc : n = N - i ∧ i < N
  swap
  · exact RelCT.of_false fun _ _ p => hc ⟨p.1, p.2.1⟩
  obtain ⟨rfl, hiN⟩ := hc
  refine (adBody_rel v K h h' hq hiN).mono (fun _ _ p => p.2.2) fun a b p => ?_
  obtain ⟨⟨ha, za⟩, hb, zb⟩ := p
  refine ⟨by simp [eval, za, zb], fun e => ?_, fun e => ?_⟩
  · have he : i + 1 = N := by simpa [eval, za] using e
    subst he; exact ⟨ha, hb⟩
  · have he : i + 1 ≠ N := by simpa [eval, za] using e
    exact ⟨N - (i + 1), by omega_using [hiN], i + 1, rfl, by omega_using [hiN, he], ha, hb⟩

/-- S2V of the associated data in both runs. -/
theorem encS2v_rel (v : UpdateImpl) (K : Calls v g) (h : EPre g s₀ C A P W D R N L) (h' : EPre g s₀' C A P W D R N L)
    (hq : EPub s₀ s₀' A N) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (encS2v g.x g.n v.callee v.ctr.callee v.ctr.suffix)
      fun a b => SDone g s₀ C A P W D R N L a ∧ SDone g s₀' C A P W D R N L b := by
  obtain ⟨_, hE⟩ : ∃ hc, (taint.check (Taint.ofRegs [.r15])
      (.block [.mov .r13 (.mem (at_ .r15 dataOff)), .mov .r14 (.mem (at_ .r15 lenOff))]) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have e := (RelCT.taint (A := taint) (P := AA g s₀ s₀' C A P W D R N L N) _
    (fun a b hab => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hab.1.r15, hab.2.r15]) hE).wp
    (F₁ := SDone g s₀ C A P W D R N L) (F₂ := SDone g s₀' C A P W D R N L)
    fun a b hab => ⟨adsEnd_wp h hab.1, adsEnd_wp h' hab.2⟩
  exact RelCT.assoc ((start_rel v.ctr K.toCCalls h h' hq.rsp).seq ((ads_rel v K h h' hq).seq
    (e.mono (fun _ _ p => p) fun _ _ p => p.2)))

theorem encryptCore_rel (v : UpdateImpl) (K : Calls v g) (h : EPre g s₀ C A P W D R N L) (h' : EPre g s₀' C A P W D R N L)
    (hq : EPub s₀ s₀' A N) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (encryptCore g.x g.n v.callee v.ctr.callee v.ctr.suffix) fun _ _ => True :=
  (encS2v_rel v K h h' hq).seq ((sealTail_rel v K h.env h'.env hq.rsp h.cp h.pw h'.pw).mono
    (fun _ _ p => ⟨p.1.spre, p.2.spre⟩) fun _ _ p => p)

/-- The copy of the IV to `siv`, in both runs: its addresses, `T` and `W`, are
the same. -/
theorem sivOut_rel {T : Addr} (q1 : s₀.gpr .rsp = s₀'.gpr .rsp) :
    RelCT isa (fun a b => OutPre s₀ W T a ∧ OutPre s₀' W T b) (.block sivOut) fun _ _ => True := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block (sivOut.take 2)) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rax, .r10]) (.block (sivOut.drop 2)) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => OutPre s₀ W T a ∧ OutPre s₀' W T b) _
    (fun a b hab => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hab.1.sp, hab.2.sp, q1]) hA).wp
    (F₁ := fun (u : State) => u.gpr .rax = T ∧ u.gpr .r10 = W)
    (F₂ := fun (u : State) => u.gpr .rax = T ∧ u.gpr .r10 = W)
    fun a b hab => ⟨sivOutHead_wp hab.1, sivOutHead_wp hab.2⟩
  have b := RelCT.taint (A := taint)
    (P := fun (a b : State) => (a.gpr .rax = T ∧ a.gpr .r10 = W) ∧ b.gpr .rax = T ∧ b.gpr .r10 = W) _
    (fun a b hab => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hab.1.1, hab.2.1]
      · rw [hab.1.2, hab.2.2]) hB
  rw [show (Code.block sivOut : Prog isa) = .block (sivOut.take 2 ++ sivOut.drop 2) by
    rw [List.take_append_drop]]
  exact RelCT.block_append ((a.mono (fun _ _ p => p) fun _ _ p => p.2).seq b)

theorem encrypt_rel (v : UpdateImpl) (K : Calls v g) (h : EPre g s₀ C A P W D R N L) (h' : EPre g s₀' C A P W D R N L)
    {T : Addr} (hT : SivArg g s₀ P W D T L) (hT' : SivArg g s₀' P W D T L) (hq : EPub s₀ s₀' A N) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (encrypt g.x g.n v.callee v.ctr.callee v.ctr.suffix) fun _ _ => True :=
  ((encryptCore_rel v K h h' hq).wp (F₁ := OutPre s₀ W T) (F₂ := OutPre s₀' W T)
    fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨encryptCore_out v K h hT, encryptCore_out v K h' hT'⟩).seq
    ((sivOut_rel hq.rsp).mono (fun _ _ p => p.2) fun _ _ p => p)

/-- The copy of the received IV to `W`, in both runs: its addresses, `T` and
`W`, are the same. -/
theorem sivIn_rel (h : EPre g s₀ C A P W D R N L) (h' : EPre g s₀' C A P W D R N L)
    {T : Addr} (hT : SivArg g s₀ P W D T L) (hT' : SivArg g s₀' P W D T L) (q1 : s₀.gpr .rsp = s₀'.gpr .rsp) :
    RelCT isa (fun a b => SDone g s₀ C A P W D R N L a ∧ SDone g s₀' C A P W D R N L b) (.block sivIn)
      fun a b => (SPre s₀ C D P W R L a ∧ Spill.Saved a.mem W s₀.gpr saved) ∧
        SPre s₀' C D P W R L b ∧ Spill.Saved b.mem W s₀'.gpr saved := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block (sivIn.take 1)) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rax, .r15]) (.block (sivIn.drop 1)) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => SDone g s₀ C A P W D R N L a ∧ SDone g s₀' C A P W D R N L b) _
    (fun a b hab => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hab.1.spre.regs.rsp, hab.2.spre.regs.rsp, q1]) hA).wp
    (F₁ := fun (u : State) => u.gpr .rax = T ∧ u.gpr .r15 = W)
    (F₂ := fun (u : State) => u.gpr .rax = T ∧ u.gpr .r15 = W)
    fun a b hab => ⟨sivInHead_wp h hT hab.1, sivInHead_wp h' hT' hab.2⟩
  have b := RelCT.taint (A := taint)
    (P := fun (a b : State) => (a.gpr .rax = T ∧ a.gpr .r15 = W) ∧ b.gpr .rax = T ∧ b.gpr .r15 = W) _
    (fun a b hab => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hab.1.1, hab.2.1]
      · rw [hab.1.2, hab.2.2]) hB
  rw [show (Code.block sivIn : Prog isa) = .block (sivIn.take 1 ++ sivIn.drop 1) by
    rw [List.take_append_drop]]
  exact ((RelCT.block_append ((a.mono (fun _ _ p => p) fun _ _ p => p.2).seq b)).wp
    (F₁ := fun (s' : State) => SPre s₀ C D P W R L s' ∧ Spill.Saved s'.mem W s₀.gpr saved)
    (F₂ := fun (s' : State) => SPre s₀' C D P W R L s' ∧ Spill.Saved s'.mem W s₀'.gpr saved)
    fun a b hab => ⟨by rw [List.take_append_drop]; exact WP.mono (sivIn_wp h hT hab.1) (fun _ p => ⟨p.1, p.2.1⟩),
      by rw [List.take_append_drop]; exact WP.mono (sivIn_wp h' hT' hab.2) (fun _ p => ⟨p.1, p.2.1⟩)⟩).mono
    (fun _ _ p => p) fun _ _ p => p.2

theorem decrypt_rel (v : UpdateImpl) (K : Calls v g) (h : EPre g s₀ C A P W D R N L) (h' : EPre g s₀' C A P W D R N L)
    {T : Addr} (hT : SivArg g s₀ P W D T L) (hT' : SivArg g s₀' P W D T L) (hq : EPub s₀ s₀' A N) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (decrypt g.x g.n v.callee v.ctr.callee v.ctr.suffix) fun _ _ => True :=
  (encS2v_rel v K h h' hq).seq ((sivIn_rel h h' hT hT' hq.rsp).seq
    ((openTail_rel v K h.env h'.env hq.rsp h.cp h.pw h'.pw).mono (fun _ _ p => ⟨p.1.1, p.2.1⟩) fun _ _ p => p))

end VG.Proof.AesSiv.X86_64

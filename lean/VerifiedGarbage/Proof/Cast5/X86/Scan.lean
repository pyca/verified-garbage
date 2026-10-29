module

public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Cast5.X86.Run
import VerifiedGarbage.Proof.Cast5.Table
public import VerifiedGarbage.Proof.Framework.X86.SseLanes
public import VerifiedGarbage.Proof.Framework.X86.SymFrame
public import VerifiedGarbage.Impl.Cast5.X86
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# CAST5 on 32-bit x86: the scan of a table

`scan sym` obtains the address `T` of `sym` in a four-byte frame below `esp`,
then visits the 256 entries of 16 bytes of the table at `T`, in order, and
leaves in each dword lane `k` of `xmm1` dword `k` of the entry whose number
is in lane `k` of `xmm0` (`scan_ok`). Vector values are kept as their four
dword lanes (`L`).
-/

@[expose] public section

namespace VG.Proof.Cast5.X86

open VG VG.X86 VG.X86.Lanes VG.X86.RegUpd VG.Impl.Cast5.X86
open VG.Impl.Cast5 (table)
open VG.Proof.Cast5 (ent Held tableEnt ent_table flatMap_range_succ)

/-! ## One entry -/

/-- Lane `k` of the result once entries `0 … j - 1` are visited. -/
def acc (tab : Nat → Nat → BitVec 32) (idx : Nat → BitVec 32) (j k : Nat) : BitVec 32 :=
  if (idx k).toNat < j then tab (idx k).toNat k else 0

/-- Every lane `n`. -/
def splat (n : Nat) : Nat → BitVec 32 := fun _ => BitVec.ofNat 32 n

theorem acc_succ (tab : Nat → Nat → BitVec 32) (idx : Nat → BitVec 32) {j : Nat} (hj : j < 256) (k : Nat) :
    (acc tab idx j k ||| (tab j k &&& if idx k = BitVec.ofNat 32 j then 0xFFFFFFFF else 0)) =
      acc tab idx (j + 1) k := by
  unfold acc
  by_cases h : idx k = BitVec.ofNat 32 j
  · have hn : (idx k).toNat = j := by rw [h, BitVec.toNat_ofNat]; omega_arith
    rw [ite_eq_left h, ite_eq_right (by omega_arith), ite_eq_left (by omega_arith), hn]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and]
    rw [show (0xFFFFFFFF : BitVec 32) = BitVec.allOnes 32 by decide, BitVec.getLsbD_allOnes]
    simp [hi]
  · have hn : (idx k).toNat ≠ j := fun h' => h (BitVec.eq_of_toNat_eq (by
      rw [h', BitVec.toNat_ofNat]; omega_arith))
    rw [ite_eq_right h, show ∀ y : BitVec 32, y &&& 0 = 0 from fun y => BitVec.eq_of_getLsbD_eq (by simp),
      show ∀ y : BitVec 32, y ||| 0 = y from fun y => BitVec.eq_of_getLsbD_eq (by simp)]
    by_cases h2 : (idx k).toNat < j
    · rw [ite_eq_left h2, ite_eq_left (by omega_arith)]
    · rw [ite_eq_right h2, ite_eq_right (by omega_arith)]

/-- What the loop of a scan keeps of a state. -/
structure LoopKeep (s t : State) : Prop where
  gpr : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r
  x0 : t.xmm .xmm0 = s.xmm .xmm0
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

theorem LoopKeep.refl (s : State) : LoopKeep s s := ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem LoopKeep.trans {s t u : State} (h : LoopKeep s t) (h' : LoopKeep t u) : LoopKeep s u :=
  ⟨fun r a b c => (h'.gpr r a b c).trans (h.gpr r a b c), h'.x0.trans h.x0, h'.mem.trans h.mem,
   h'.rd.trans h.rd, h'.wr.trans h.wr, h'.syms.trans h.syms⟩

theorem LoopKeep.setXmm (s : State) {x : XReg} (v : BitVec 128) (hx : x ≠ .xmm0) : LoopKeep s (s.setXmm x v) :=
  ⟨fun _ _ _ _ => rfl, xmm_setXmm_of_ne _ _ (Ne.symm hx), rfl, rfl, rfl, rfl⟩

theorem LoopKeep.setReg (s : State) {r : Reg} (v : BitVec 32) (hr : r = .eax ∨ r = .ecx ∨ r = .edx) :
    LoopKeep s (s.setReg r v) :=
  ⟨fun _ a b c => gpr_setReg_of_ne _ _ (by rcases hr with rfl | rfl | rfl <;> with_reducible assumption), rfl, rfl, rfl, rfl,
    rfl⟩

theorem LoopKeep.setFlags (s : State) (a b c d : Option Bool) : LoopKeep s (s.setFlags a b c d) :=
  ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem LoopKeep.arithFlags (s : State) (v : BitVec 32) (c o : Bool) : LoopKeep s (arithFlags s v c o) :=
  ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `LoopKeep s t` for `t` made from `s` by writes of `eax`, `ecx`, `edx`, the
flags and registers other than `xmm0`. -/
tactic_template "loop_keep" : tactic => `(tactic| (
                   refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
                   · intro r ha hc hd
                     simp only [gpr_setXmm, gpr_setReg, ha, hc, hd, gpr_setFlags, gpr_arithFlags, ite_false]
                   all_goals simp (disch := decide) only [xmm_setXmm_of_ne, xmm_setReg', xmm_setFlags',
                     xmm_arithFlags', mem_setXmm, mem_setReg, mem_setFlags, mem_arithFlags, rd_setXmm, rd_setReg, rd_setFlags,
                     rd_arithFlags, wr_setXmm, wr_setReg, wr_setFlags, wr_arithFlags, syms_setXmm', syms_setReg',
                     syms_setFlags', syms_arithFlags']))

/-- The state of the scan with entries `0 … j - 1` visited, from `s₀`. -/
structure ScanAt (s₀ : State) (tab : Nat → Nat → BitVec 32) (idx : Nat → BitVec 32) (j : Nat)
    (s : State) : Prop where
  x0 : s.xmm .xmm0 = L idx
  x1 : s.xmm .xmm1 = L (acc tab idx j)
  x2 : s.xmm .xmm2 = L (splat j)
  x3 : s.xmm .xmm3 = L (splat 1)
  x6 : s.xmm .xmm6 = L (splat 0xFFFFFFFF)
  keep : LoopKeep s₀ s

theorem entry_ok {s₀ s : State} {tab : Nat → Nat → BitVec 32} {idx : Nat → BitVec 32} {j : Nat} (e : Nat)
    (hj : j < 256) (hidx : ∀ k < 4, (idx k).toNat < 256) (h : ScanAt s₀ tab idx j s)
    (hr : InRegions (s.rd ++ s.wr) (addr (s.gpr .ecx) (16 * e)) 16)
    (hv : ∀ k < 4, s.mem.readW (addr (s.gpr .ecx) (16 * e) + BitVec.ofNat 64 (4 * k)) 32 = tab j k) :
    WP isa (.block (scanEntry e)) s fun t => ScanAt s₀ tab idx (j + 1) t ∧ t.gpr = s.gpr := by
  obtain ⟨h0, h1, h2, h3, h6, hk⟩ := h
  unfold scanEntry
  crun [hr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := decide) only [xmm_setXmm_self, xmm_setXmm_of_ne, movdqa_L]
  · exact h0
  · rw [h0, h1, h2, h6, pxor_L, paddd_L, psrld_L, pslld_L, por_L, readW128_L, pand_L, por_L]
    refine L_congr fun k hk => ?_
    rw [hv k hk, show splat j k = BitVec.ofNat 32 j from rfl,
      show splat 0xFFFFFFFF k = (0xFFFFFFFF : BitVec 32) from rfl, mask_eq (hidx k hk) hj]
    exact acc_succ tab idx hj k
  · rw [h2, h3, paddd_L]
    refine L_congr fun k _ => ?_
    simp only [splat, BitVec.ofNat_add]
  · exact h3
  · exact h6
  · exact hk.trans (by loop_keep)

theorem entries_ok {s₀ s : State} {tab : Nat → Nat → BitVec 32} {idx : Nat → BitVec 32} {q : Nat}
    (hq : q < 64) (hidx : ∀ k < 4, (idx k).toNat < 256)
    (hr : ∀ e < 4, InRegions (s.rd ++ s.wr) (addr (s.gpr .ecx) (16 * e)) 16)
    (hv : ∀ e < 4, ∀ k < 4,
      s.mem.readW (addr (s.gpr .ecx) (16 * e) + BitVec.ofNat 64 (4 * k)) 32 = tab (4 * q + e) k) :
    ∀ e ≤ 4, ScanAt s₀ tab idx (4 * q) s →
      WP isa (.block ((List.range e).flatMap scanEntry)) s
        fun t => ScanAt s₀ tab idx (4 * q + e) t ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  intro e he h
  induction e with
  | zero => exact WP.block_nil ⟨h, rfl, rfl, rfl, rfl⟩
  | succ e ih =>
    rw [flatMap_range_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega_arith)) fun t ⟨ht, hg, hm, hrd, hwr⟩ => ?_
    have hr' : InRegions (t.rd ++ t.wr) (addr (t.gpr .ecx) (16 * e)) 16 := by
      rw [hrd, hwr, hg]; exact hr e (by omega_arith)
    refine WP.mono (entry_ok e (by omega_arith) hidx ht hr' (fun k hk => by rw [hm, hg]; exact hv e (by omega_arith) k hk))
      fun u ⟨hu, hug⟩ => ⟨hu, hug.trans hg, ?_⟩
    refine ⟨by rw [hu.keep.mem, ← ht.keep.mem, hm], by rw [hu.keep.rd, ← ht.keep.rd, hrd],
      by rw [hu.keep.wr, ← ht.keep.wr, hwr]⟩

theorem ScanAt.keepTo {s₀ s t : State} {tab : Nat → Nat → BitVec 32} {idx : Nat → BitVec 32} {j : Nat}
    (h : ScanAt s₀ tab idx j s) (hk : LoopKeep s t) (h1 : t.xmm .xmm1 = s.xmm .xmm1)
    (h2 : t.xmm .xmm2 = s.xmm .xmm2) (h3 : t.xmm .xmm3 = s.xmm .xmm3) (h6 : t.xmm .xmm6 = s.xmm .xmm6) :
    ScanAt s₀ tab idx j t :=
  ⟨hk.x0.trans h.x0, h1.trans h.x1, h2.trans h.x2, h3.trans h.x3, h6.trans h.x6, h.keep.trans hk⟩

/-- The address of entry `e` of group `q` of the table at `T`. -/
theorem entry_addr {T : BitVec 32} (hT : T.toNat + 4096 ≤ 2 ^ 32) {q e : Nat} (hq : q < 64) (he : e < 4) :
    addr (T + BitVec.ofNat 32 (64 * q)) (16 * e) = T.setWidth 64 + BitVec.ofNat 64 (64 * q + 16 * e) := by
  rw [show addr (T + BitVec.ofNat 32 (64 * q)) (16 * e) = addr T (64 * q + 16 * e) by
    simp only [addr, BitVec.add_assoc, BitVec.ofNat_add]]
  exact addr_eq (by omega_arith)

/-- The entries of the table at `T`, as dwords. -/
def TabAt (m : Mem) (T : BitVec 32) (tab : Nat → Nat → BitVec 32) : Prop :=
  ∀ j < 256, ∀ k < 4, m.readW (T.setWidth 64 + BitVec.ofNat 64 (16 * j + 4 * k)) 32 = tab j k

theorem body_ok {s₀ s : State} {tab : Nat → Nat → BitVec 32} {idx : Nat → BitVec 32} {T : BitVec 32} {q : Nat}
    (hq : q < 64) (hidx : ∀ k < 4, (idx k).toNat < 256) (hfit : T.toNat + 4096 ≤ 2 ^ 32)
    (hT : InRegions (s₀.rd ++ s₀.wr) (T.setWidth 64) 4096) (htab : TabAt s₀.mem T tab)
    (hecx : s.gpr .ecx = T + BitVec.ofNat 32 (64 * q)) (h : ScanAt s₀ tab idx (4 * q) s) :
    WP isa (.block scanBody) s fun t => ScanAt s₀ tab idx (4 * (q + 1)) t ∧
      t.gpr .ecx = T + BitVec.ofNat 32 (64 * (q + 1)) ∧ t.gpr .edx = s.gpr .edx - 1 ∧
      t.zf = some (s.gpr .edx - 1 == 0) := by
  unfold scanBody
  rw [WP.block_append_iff]
  have hr : ∀ e < 4, InRegions (s.rd ++ s.wr) (addr (s.gpr .ecx) (16 * e)) 16 := fun e he => by
    rw [h.keep.rd, h.keep.wr, hecx, entry_addr hfit hq he]
    exact CallLay.inRegions_sub hT (by omega_arith) (by decide)
  have hv : ∀ e < 4, ∀ k < 4,
      s.mem.readW (addr (s.gpr .ecx) (16 * e) + BitVec.ofNat 64 (4 * k)) 32 = tab (4 * q + e) k :=
    fun e he k hk => by
      rw [h.keep.mem, hecx, entry_addr hfit hq he, Offset.add_add,
        show 64 * q + 16 * e + 4 * k = 16 * (4 * q + e) + 4 * k by omega_arith]
      exact htab _ (by omega_arith) k hk
  refine WP.mono (entries_ok hq hidx hr hv 4 (Nat.le_refl _) h) fun t ⟨ht, hg, _, _, _⟩ => ?_
  crun
  rw [hg, hecx, BitVec.add_assoc, ← BitVec.ofNat_add, show 64 * q + 64 = 64 * (q + 1) by omega_arith]
  exact ⟨ht.keepTo (by loop_keep) rfl rfl rfl rfl, rfl, rfl, rfl⟩

theorem acc_zero (tab : Nat → Nat → BitVec 32) (idx : Nat → BitVec 32) : L (acc tab idx 0) = 0 := by
  rw [show (0 : BitVec 128) = L fun _ => 0 by decide]
  exact L_congr fun k _ => by simp [acc]

/-- The setup of the scan: the table's address (from `eax`) in `ecx`, 64
groups to go in `edx`, nothing found yet, entry 0 next, one and all ones. -/
theorem start_ok (s : State) (tab : Nat → Nat → BitVec 32) {idx : Nat → BitVec 32} (h0 : s.xmm .xmm0 = L idx) :
    WP isa (.block scanStart) s fun t =>
      ScanAt s tab idx 0 t ∧ t.gpr .ecx = s.gpr .eax ∧ t.gpr .edx = 64 := by
  unfold scanStart
  crun
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, by loop_keep⟩, rfl⟩ <;>
    simp (disch := decide) only [xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg']
  · exact h0
  · rw [acc_zero, XBinOp.eval, BitVec.xor_self]; rfl
  · rw [show L (splat 0) = 0 by decide, XBinOp.eval, BitVec.xor_self]; rfl
  · exact bcast_L _
  · exact bcast_L _

/-- What a scan keeps of a state. -/
structure ScanKeep (s t : State) : Prop where
  gpr : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r
  x0 : t.xmm .xmm0 = s.xmm .xmm0
  mem : Frame [below (s.gpr .esp) 4] s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

/-- The table's frame, with what it keeps of the vector registers. -/
theorem symFrame_ok' (name : String) (s : State) (hsp : 4 ≤ (s.gpr .esp).toNat) :
    WP isa (.frame (.symPush .eax name) (.block []) (.pop .ecx 1)) s fun t =>
      SymAddrPost name s t ∧ t.xmm = s.xmm := by
  have hp : isa.push (.symPush .eax name) s = some (symPushed name s) := by
    simp [isa, push, symPushed, hsp, below]
  have hq : isa.pop (.pop .ecx 1) (symPushed name s) (symPushed name s) = some (symPopped name s) := by
    simp [isa, pop, symPushed, symPopped, State.setReg, arithFlags, below]
  obtain ⟨tr, t, he, hpost⟩ := symFrame_ok name s hsp
  have ht := (Exec.det he (Exec.frame hp (Exec.block (is := []) rfl) hq)).2
  refine ⟨tr, t, he, hpost, ?_⟩
  rw [ht]
  simp [symPopped, popReg, symPushed, State.setReg, arithFlags, State.setFlags]

/-- The scan: lane `k` of `xmm1` is dword `k` of the entry of the table at
`sym` whose number is lane `k` of `xmm0`. -/
theorem scan_ok (s : State) (sym : String) {tab : Nat → Nat → BitVec 32} {idx : Nat → BitVec 32}
    (h0 : s.xmm .xmm0 = L idx) (hidx : ∀ k < 4, (idx k).toNat < 256) (hsp : 4 ≤ (s.gpr .esp).toNat)
    (hfit : (s.syms sym).toNat + 4096 ≤ 2 ^ 32)
    (hT : InRegions (s.rd ++ s.wr) ((s.syms sym).setWidth 64) 4096)
    (hdis : Region.Disjoint ⟨(s.syms sym).setWidth 64, 4096⟩ (below (s.gpr .esp) 4))
    (htab : TabAt s.mem (s.syms sym) tab) :
    WP isa (scan sym) s fun t => t.xmm .xmm1 = L (fun k => tab (idx k).toNat k) ∧ ScanKeep s t := by
  unfold scan
  refine WP.seq (WP.mono (symFrame_ok' sym s hsp) fun u ⟨hu, hux⟩ => ?_)
  have hu0 : u.xmm .xmm0 = L idx := by rw [hux]; exact h0
  have hT' : InRegions (u.rd ++ u.wr) ((u.syms sym).setWidth 64) 4096 := by rw [hu.rd, hu.wr, hu.syms]; exact hT
  have htab' : TabAt u.mem (u.syms sym) tab := fun j hj k hk => by
    rw [hu.syms, ← htab j hj k hk]
    refine hu.frame.readW (r := ⟨(s.syms sym).setWidth 64, 4096⟩) ?_ ?_ (by decide)
    · exact Offset.contains_base _ (by omega_arith) (by omega_arith)
    · intro r hr; rw [List.mem_singleton] at hr; subst hr; exact hdis
  have hfit' : (u.syms sym).toNat + 4096 ≤ 2 ^ 32 := by rw [hu.syms]; exact hfit
  refine WP.seq (WP.mono (start_ok u tab hu0) fun v ⟨hv, hvc, hvd⟩ => ?_)
  rw [hu.addr] at hvc
  refine wp_countdown (cnt := .edx) (N := 64) (by decide) (by decide)
    (fun q w => ScanAt u tab idx (4 * q) w ∧ w.gpr .ecx = u.syms sym + BitVec.ofNat 32 (64 * q))
    (fun q hq w ⟨hw, hwc⟩ _ => WP.mono (body_ok hq hidx hfit' hT' htab' hwc hw) fun x ⟨hx, hxc, hxd, hz⟩ =>
      ⟨⟨hx, hxc⟩, hxd, hz⟩)
    (fun w ⟨hw, _⟩ => ⟨?_, ?_⟩) ⟨hv, by rw [hvc, hu.syms]; exact (BitVec.add_zero _).symm⟩ (by rw [hvd]; rfl)
  · rw [hw.x1]
    exact L_congr fun k hk => by rw [acc, ite_eq_left (by have := hidx k hk; omega_arith)]
  · exact ⟨fun r a b c => (hw.keep.gpr r a b c).trans (hu.gpr r (by simp [a, b])), hw.keep.x0.trans (by rw [hux]),
      by rw [hw.keep.mem]; exact hu.frame, hw.keep.rd.trans hu.rd, hw.keep.wr.trans hu.wr,
      hw.keep.syms.trans hu.syms⟩

end VG.Proof.Cast5.X86

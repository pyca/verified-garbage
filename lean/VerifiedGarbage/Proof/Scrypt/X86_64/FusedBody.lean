module
public import VerifiedGarbage.Proof.Scrypt.X86_64.FusedInvariant
public import VerifiedGarbage.Proof.Scrypt.X86_64.FusedLoop
import VerifiedGarbage.Proof.Scrypt.Memory
import VerifiedGarbage.Proof.Scrypt.X86_64.FusedInit
import VerifiedGarbage.Proof.MdStream.X86_64.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Scrypt.X86_64.FusedHalf
import VerifiedGarbage.Proof.Scrypt.X86_64.FusedSetup

/-! ### `Scrypt.X86_64.FusedTail`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Scrypt.X86_64.Retained
open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Proof.MdStream.X86_64 (wp_movm wp_addi wp_subi wp_store)

abbrev MetaOff (n : Nat) : Prop := n = 16 ∨ n = 24 ∨ n = 32 ∨ n = 40

def metaR (p : Addr) : Region := ⟨bufAt p 16, 32⟩

theorem meta_contains (p : Addr) {off : Nat} (h : MetaOff off) :
    (metaR p).Contains (bufAt p off) 8 := by
  have h1 : 16 ≤ off := by rcases h with rfl | rfl | rfl | rfl <;> decide
  have h2 : off + 8 ≤ 48 := by rcases h with rfl | rfl | rfl | rfl <;> decide
  simpa only [metaR, bufAt, ofInt_natCast] using Offset.contains p h1 h2 (by decide)

theorem meta_read_write (m : Mem) (p : Addr) {i j : Nat} (hi : MetaOff i) (hj : MetaOff j) (v : Addr) :
    (m.writeW (bufAt p i) v).readW (bufAt p j) 64 = if i = j then v else m.readW (bufAt p j) 64 := by
  by_cases h : i = j
  · subst j; rw [ite_eq_left rfl, Mem.readW_writeW_self64]
  · rw [ite_eq_right h]
    apply Mem.readW_writeW_sep _ (by decide)
    simp only [bufAt, ofInt_natCast]
    exact Offset.sep p (by rcases hi with rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl <;> omega_arith)
      (by rcases hj with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hi with rfl | rfl | rfl | rfl <;> decide)

theorem Meta.write {p b e o count : Addr} {m : Mem} (h : Meta p b e o count m)
    {off : Nat} (ho : MetaOff off) (v : Addr) :
    Meta p (if off = 16 then v else b) (if off = 24 then v else e)
      (if off = 32 then v else o) (if off = 40 then v else count) (m.writeW (bufAt p off) v) := by
  exact ⟨by rw [meta_read_write m p ho (by decide), h.input],
    by rw [meta_read_write m p ho (by decide), h.even],
    by rw [meta_read_write m p ho (by decide), h.odd],
    by rw [meta_read_write m p ho (by decide), h.count]⟩

structure TailStep (p : Addr) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, r ≠ .rax → s.gpr r = s₀.gpr r
  frame : Frame [metaR p] s₀.mem s.mem

theorem TailStep.trans {p : Addr} {s t u : State} (h : TailStep p s t) (h' : TailStep p t u) : TailStep p s u :=
  ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, fun r hr => (h'.keep r hr).trans (h.keep r hr), h.frame.trans h'.frame⟩

theorem advance_ok {p : Addr} {s : State} (si : s.gpr .rsi = p) (hs : InRegions s.wr p 64)
    (off inc : Nat) (ho : MetaOff off) (hn : inc = 64 ∨ inc = 128) :
    WP isa (.block (fusedAdvance off inc)) s fun t => TailStep p s t ∧
      t.mem = s.mem.writeW (bufAt p off) (s.mem.readW (bufAt p off) 64 + BitVec.ofNat 64 inc) := by
  have bound : off + 8 ≤ 64 := by rcases ho with rfl | rfl | rfl | rfl <;> decide
  unfold fusedAdvance
  refine wp_movm (a := bufAt p off) (by rw [ea_at, si])
    (Memory.InRegions.right (access hs bound (by omega_using [bound]))) fun a ua => wp_addi fun b ub => ?_
  have si' : b.gpr .rsi = p := by rw [ub.other _ (by decide), ua.other _ (by decide), si]
  refine wp_store (a := bufAt p off) (by rw [ea_at, si'])
    (by rw [ub.wr, ua.wr]; exact access hs bound (by omega_using [bound])) fun t gt mt rt wt => WP.block_nil ?_
  have val : b.gpr .rax = s.mem.readW (bufAt p off) 64 + BitVec.ofNat 64 inc := by
    rw [ub.gpr, ua.gpr]; rcases hn with rfl | rfl <;> rfl
  rw [val, ub.mem, ua.mem] at mt
  exact ⟨⟨rt.trans (ub.rd.trans ua.rd), wt.trans (ub.wr.trans ua.wr),
    fun r hr => by rw [gt, ub.other r hr, ua.other r hr],
    by rw [mt]; exact (Frame.refl _ _).writeW (by simp) _ (meta_contains p ho)⟩, mt⟩

theorem decrement_ok {p : Addr} {s : State} (si : s.gpr .rsi = p) (hs : InRegions s.wr p 64) :
    WP isa (.block [.mov .rax (.mem (at_ .rsi 40)), .alu .sub .rax (.imm 1), .store (at_ .rsi 40) .rax]) s
      fun t => TailStep p s t ∧
        t.mem = s.mem.writeW (bufAt p 40) (s.mem.readW (bufAt p 40) 64 - 1) ∧
        t.zf = some (s.mem.readW (bufAt p 40) 64 - 1 == 0) := by
  refine wp_movm (a := bufAt p 40) (by rw [ea_at, si])
    (Memory.InRegions.right (access hs (by decide))) fun a ua => wp_subi fun b ub hz => ?_
  have hea : b.ea (at_ .rsi 40) = bufAt p 40 := by
    rw [ea_at, ub.other _ (by decide), ua.other _ (by decide), si]
  have hw : InRegions b.wr (bufAt p 40) 8 := by
    rw [ub.wr, ua.wr]; exact access hs (by decide)
  have val : b.gpr .rax = s.mem.readW (bufAt p 40) 64 - 1 := by
    rw [ub.gpr, ua.gpr]; rfl
  refine VG.Proof.MdStream.X86_64.WP.cons (s' := { b with mem := b.mem.writeW (bufAt p 40) (b.gpr .rax) })
    (by simp only [exec, State.store64, hea, hw, ite_true]) (WP.block_nil ?_)
  have mt : b.mem.writeW (bufAt p 40) (b.gpr .rax) =
      s.mem.writeW (bufAt p 40) (s.mem.readW (bufAt p 40) 64 - 1) := by rw [val, ub.mem, ua.mem]
  refine ⟨⟨ub.rd.trans ua.rd, ub.wr.trans ua.wr,
    fun r hr => by rw [ub.other r hr, ua.other r hr], ?_⟩, mt, ?_⟩
  · rw [mt]; exact (Frame.refl _ _).writeW (by simp) _ (meta_contains p (by decide))
  · rw [hz, ua.gpr]; rfl

theorem tail_ok {p b e o count : Addr} {s : State} (si : s.gpr .rsi = p)
    (hs : InRegions s.wr p 64) (hm : Meta p b e o count s.mem) :
    WP isa (.block fusedTail) s fun t => TailStep p s t ∧
      Meta p (b + 128) (e + 64) (o + 64) (count - 1) t.mem ∧
      t.zf = some (count - 1 == 0) := by
  unfold fusedTail
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  apply (advance_ok si hs 16 128 (by decide) (by decide)).mono
  intro a ⟨ha, ma⟩
  have hma : Meta p (b + 128) e o count a.mem := by
    rw [ma, hm.input]; exact hm.write (off := 16) (by decide) (b + 128)
  rw [WP.block_append_iff]
  apply (advance_ok (p := p) (by rw [ha.keep _ (by decide), si]) (by rw [ha.wr]; exact hs)
    24 64 (by decide) (by decide)).mono
  intro c ⟨hc, mc⟩
  have hmc : Meta p (b + 128) (e + 64) o count c.mem := by
    rw [mc, hma.even]; exact hma.write (off := 24) (by decide) (e + 64)
  have hac := ha.trans hc
  rw [WP.block_append_iff]
  apply (advance_ok (p := p) (by rw [hac.keep _ (by decide), si]) (by rw [hac.wr]; exact hs)
    32 64 (by decide) (by decide)).mono
  intro d ⟨hd, md⟩
  have hmd : Meta p (b + 128) (e + 64) (o + 64) count d.mem := by
    rw [md, hmc.odd]; exact hmc.write (off := 32) (by decide) (o + 64)
  have had := hac.trans hd
  apply (decrement_ok (p := p) (by rw [had.keep _ (by decide), si]) (by rw [had.wr]; exact hs)).mono
  intro t ⟨ht, mt, hz⟩
  refine ⟨had.trans ht, ?_, ?_⟩
  · rw [mt, hmd.count]; exact hmd.write (off := 40) (by decide) (count - 1)
  · rw [hmd.count] at hz; exact hz

theorem TailStep.scratch {p : Addr} {s t : State} (h : TailStep p s t) : Frame [⟨p, 64⟩] s.mem t.mem :=
  h.frame.sub fun R hR => by
    simp only [List.mem_singleton] at hR; subst R
    exact ⟨⟨p, 64⟩, by simp, by simpa only [metaR, bufAt, ofInt_natCast] using
      (Offset.sub_base p (d := 16) (n := 32) (k := 64) (by decide))⟩

theorem Words.tail {p : Addr} {v : Vector Spec.Scrypt.Word 16} {s t : State}
    (h : Words p v s) (ht : TailStep p s t) : Words p v t := by
  refine ⟨fun k hk => (ht.keep _ (wreg_ne k hk).1).trans (h.regs k hk), ?_,
    (ht.keep _ (by decide)).trans h.rsi⟩
  intro k hk h12
  rw [ht.frame.readW (r := slotR p) (by
    simpa only [slotR, bufAt, ofInt_natCast] using
      Offset.contains_base p (d := slotOff k) (n := 4) (k := 16)
        (by simp only [slotOff]; omega_using [hk]) (by simp only [slotOff]; omega_using [hk])) (fun R hR => by
    simp only [List.mem_singleton] at hR; subst R
    simpa only [slotR, metaR, bufAt, ofInt_natCast, BitVec.add_zero] using
      Offset.disjoint p (d := 0) (n := 16) (e := 16) (k := 32) (by decide) (by decide) (by decide)) (by decide)]
  exact h.slots k hk h12
end VG.Proof.Scrypt.X86_64.Retained

end

end


@[expose] public section

namespace VG.Proof.Scrypt.X86_64.BlockMix.Fused
open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (bytesAt)
open VG.Proof.Scrypt.X86_64.Retained (Words Meta memWords)

/-- Lift only the core's actual writes into the established BlockMix frame. -/
theorem core_frame {s₀ : State} {off : Nat} {m m' : Mem}
    (hf : Frame [VG.Proof.Scrypt.X86_64.bR (yP s₀ + BitVec.ofNat 64 off), VG.Proof.Scrypt.X86_64.slotR (sc s₀),
      Retained.tempR (sc s₀)] m m') :
    Frame [slot s₀ off, ⟨sc s₀, 64⟩, stkR s₀] m m' := by
  apply hf.sub
  intro R hR
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl | rfl
  · exact ⟨slot s₀ off, by simp, fun _ h => h⟩
  · exact ⟨⟨sc s₀, 64⟩, by simp, Region.sub_prefix (by decide)⟩
  · exact ⟨⟨sc s₀, 64⟩, by simp, by simpa only [Retained.tempR, bufAt, ofInt_natCast] using
      (Offset.sub_base (sc s₀) (d := 48) (n := 8) (k := 64) (by decide))⟩

theorem half_ok {s₀ s : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀)
    (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) {prev : Addr}
    (words : Words (sc s₀) (memWords s.mem prev) s)
    (metadata : Meta (sc s₀) (bB s₀ k) (yE s₀ k) (yO s₀ k) (BitVec.ofNat 64 (rr s₀ - k)) s.mem)
    (odd : Bool) :
    WP isa (fusedHalf (if odd then 64 else 0) odd) s fun t =>
      Words (sc s₀) (memWords t.mem (if odd then yO s₀ k else yE s₀ k)) t ∧
      bytesAt t.mem (if odd then yO s₀ k else yE s₀ k) 64 = Spec.Scrypt.salsa
        (Spec.Pbkdf2.xorBytes (bytesAt s.mem prev 64)
          (bytesAt s.mem (bB s₀ k + BitVec.ofNat 64 (if odd then 64 else 0)) 64)) ∧
      Frame [VG.Proof.Scrypt.X86_64.bR (if odd then yO s₀ k else yE s₀ k), VG.Proof.Scrypt.X86_64.slotR (sc s₀),
        Retained.tempR (sc s₀)] s.mem t.mem ∧
      Meta (sc s₀) (bB s₀ k) (yE s₀ k) (yO s₀ k) (BitVec.ofNat 64 (rr s₀ - k)) t.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .rsp = s.gpr .rsp := by
  apply Retained.half_ok words metadata _ (by cases odd <;> simp) odd
  · rw [rd, wr, hp.rd, hp.wr]
    refine ⟨bR s₀, by simp, ?_⟩
    simp only [bB, Memory.add_ofNat]
    exact in_b hp (by cases odd <;> simp <;> omega_using [hk])
  · rw [wr, hp.wr]
    refine ⟨yR s₀, by simp, ?_⟩
    cases odd <;> exact in_y hp (by omega_using [hk])
  · rw [wr, hp.wr]
    exact ⟨scR s₀, by simp, by simpa only [BitVec.add_zero] using in_s s₀ (o := 0) (n := 64) (by decide)⟩
  · cases odd <;> exact slot_s hp (by omega_using [hk])
  · simp only [bB, Memory.add_ofNat]
    cases odd <;> exact (yb_disj hp (by omega_using [hk]) (by simp; omega_using [hk])).symm
  · simp only [bB, Memory.add_ofNat]
    exact (hp.b_s.sub_left (b_sub hp (by cases odd <;> simp <;> omega_using [hk]))).sub_right
      (Region.sub_prefix (by decide))

theorem body_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s : State} (h : Inv s₀ k s) :
    WP isa fusedBody s fun t => Inv s₀ (k + 1) t ∧
      t.zf = some (BitVec.ofNat 64 (rr s₀ - k) - 1 == 0) := by
  unfold fusedBody
  refine WP.seq (WP.mono (half_ok hp hk h.rd h.wr h.words h.metadata false) fun a ha => ?_)
  obtain ⟨wa, ba, fa, ma, ra, wra, spa⟩ := ha
  simp only [Bool.false_eq_true, ite_false, BitVec.add_zero] at wa ba fa
  refine WP.seq (WP.mono (half_ok hp hk (ra.trans h.rd) (wra.trans h.wr) wa ma true) fun b hb => ?_)
  obtain ⟨wb, bb, fb, mb, rb, wrb, spb⟩ := hb
  simp only [ite_true] at wb bb fb
  have baddr : bB s₀ k + BitVec.ofNat 64 64 = bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1)) := by
    rw [bB, Memory.add_ofNat]; congr 2; omega_using []
  rw [baddr] at bb
  obtain ⟨ff, saved, done⟩ := mem_ok hp hk h.toLogical.old (core_frame fa) ba (core_frame fb) bb
  have logical : Logical s₀ (k + 1) b :=
    ⟨by omega_using [hk], rb.trans (ra.trans h.rd), wrb.trans (wra.trans h.wr), spb.trans (spa.trans h.rsp),
      ff, saved, done, by show bytesAt b.mem (yO s₀ k) 64 = _; rw [(done k (by omega_using [])).2]; rfl⟩
  have hs : InRegions b.wr (sc s₀) 64 := by
    rw [logical.wr, hp.wr]; exact ⟨scR s₀, by simp, by simpa only [BitVec.add_zero] using in_s s₀ (o := 0) (n := 64) (by decide)⟩
  refine WP.mono (Retained.tail_ok wb.rsi hs mb) fun t ⟨ht, mt, hz⟩ => ?_
  have lt := r_lt hp
  have nextb : bB s₀ k + 128 = bB s₀ (k + 1) := by
    change bP s₀ + BitVec.ofNat 64 (128 * k) + BitVec.ofNat 64 128 = _
    rw [Memory.add_ofNat]; congr 2
  have nexte : yE s₀ k + 64 = yE s₀ (k + 1) := by
    change yP s₀ + BitVec.ofNat 64 (64 * k) + BitVec.ofNat 64 64 = _
    rw [Memory.add_ofNat]; congr 2
  have nexto : yO s₀ k + 64 = yO s₀ (k + 1) := by
    change yP s₀ + BitVec.ofNat 64 (64 * (rr s₀ + k)) + BitVec.ofNat 64 64 = _
    rw [Memory.add_ofNat]; congr 2
  have nextc : BitVec.ofNat 64 (rr s₀ - k) - 1 = BitVec.ofNat 64 (rr s₀ - (k + 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, Memory.toNat_ofNat_lt (by omega_using [lt]), Memory.toNat_ofNat_lt (by omega_using [lt]),
      show (1 : BitVec 64).toNat = 1 from rfl]
    omega_using [hk, lt]
  rw [nextb, nexte, nexto, nextc] at mt
  refine ⟨⟨logical.scratch hp ht.scratch ht.rd ht.wr (ht.keep _ (by decide)), ?_, mt⟩, hz⟩
  have mw := memWords_frame ht.scratch (p := yO s₀ k) (fun R hR => by
    simp only [List.mem_singleton] at hR; subst R; exact slot_s hp (by omega_using [hk]))
  change Words (sc s₀) (memWords t.mem (yO s₀ k)) t
  rw [mw]; exact wb.tail ht
end VG.Proof.Scrypt.X86_64.BlockMix.Fused

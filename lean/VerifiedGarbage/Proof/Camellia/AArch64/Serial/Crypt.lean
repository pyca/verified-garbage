module

public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Rounds
import VerifiedGarbage.Proof.Framework.Interleave
public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Camellia.SerialPure
public import VerifiedGarbage.Spec.Camellia.Ctr
import VerifiedGarbage.Proof.Camellia.CtrCipher
public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.State
public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Lookup
import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Lookup
import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Load
import VerifiedGarbage.Proof.Sm4.AArch64.Imm
import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Camellia.AArch64.Serial.Body`, which only this module used -/

section

/-! ### `Camellia.AArch64.Serial.Kernel`, which only this module used -/

section

/-! # Composition of the serial core's read-only arithmetic kernel -/

@[expose] public section
namespace VG.Proof.Camellia.AArch64.Serial
open VG VG.AArch64 VG.Impl.Camellia.AArch64.Serial

structure Stable (s t : State) : Prop where
  regs : ∀ r, r ∉ written → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem Stable.trans {s t u : State} (h : Stable s t) (g : Stable t u) : Stable s u :=
  ⟨fun r hr => (g.regs r hr).trans (h.regs r hr),g.mem.trans h.mem,
    g.rd.trans h.rd,g.wr.trans h.wr,g.sp.trans h.sp⟩

theorem Stable.keys {s t : State} (h : Stable s t) : keyWord t = keyWord s := by
  funext j
  simp only [keyWord,h.mem,h.regs .x5 (by decide)]

structure Context (s : State) : Prop where
  constants : Constants s
  masks : Masks s
  table : Table s
  read : ∀ j < 34, InRegions (s.rd ++ s.wr) (s.gpr .x5+BitVec.ofNat 64 (256+8*j)) 8

theorem Context.read_stable {s t : State} (h : Context s) (hs : Stable s t) :
    ∀ j < 34, InRegions (t.rd ++ t.wr) (t.gpr .x5+BitVec.ofNat 64 (256+8*j)) 8 := by
  intro j hj
  rw [hs.rd,hs.wr,hs.regs .x5 (by decide)]
  exact h.read j hj

theorem six_step {s : State} (h : Context s) (k : Nat) (hk : k+6 ≤ 34) :
    ∃ t, runBlock isa (six k) s = some t ∧ Context t ∧ Stable s t ∧
      halves t = pairs (keyWord s) k 3 (halves s) := by
  obtain ⟨t,he,hv,hc,hm,ht,hg,hmem,hrd,hwr,hsp⟩ :=
    six_run s k hk h.constants h.masks h.table h.read
  have hs : Stable s t := ⟨hg,hmem,hrd,hwr,hsp⟩
  exact ⟨t,he,⟨hc,hm,ht,h.read_stable hs⟩,hs,hv⟩

theorem fl_step {s : State} (h : Context s) (k : Nat) (hk : k+1 < 34) :
    ∃ t, runBlock isa (flPair k) s = some t ∧ Context t ∧ Stable s t ∧
      halves t = (Spec.Camellia.fl (halves s).1 (keyWord s k),
        Spec.Camellia.flinv (halves s).2 (keyWord s (k+1))) := by
  obtain ⟨t,he,hv,hc,hm,ht,hg,hmem,hrd,hwr,hsp⟩ :=
    flPair_run s k hk h.constants h.masks h.table h.read
  have hs : Stable s t := ⟨hg,hmem,hrd,hwr,hsp⟩
  exact ⟨t,he,⟨hc,hm,ht,h.read_stable hs⟩,hs,hv⟩

theorem partial_run {s : State} (h : Context s) :
    ∃ t, runBlock isa (six 2 ++ flPair 8 ++ six 10 ++ flPair 16 ++ six 18) s = some t ∧
      Context t ∧ Stable s t ∧ halves t = partialRounds (keyWord s) (halves s) := by
  obtain ⟨a,ae,ac,as,av⟩ := six_step h 2 (by decide)
  obtain ⟨b,be,bc,bs,bv⟩ := fl_step ac 8 (by decide)
  obtain ⟨c,ce,cc,cs,cv⟩ := six_step bc 10 (by decide)
  obtain ⟨d,de,dc,ds,dv⟩ := fl_step cc 16 (by decide)
  obtain ⟨e,ee,ec,es,ev⟩ := six_step dc 18 (by decide)
  have ab := as.trans bs
  have abc := ab.trans cs
  have abcd := abc.trans ds
  refine ⟨e,?_,ec,abcd.trans es,?_⟩
  · rw [VG.Interleave.runBlock_append,VG.Interleave.runBlock_append,
      VG.Interleave.runBlock_append,VG.Interleave.runBlock_append,
      ae,Option.bind_some,be,Option.bind_some,ce,Option.bind_some,de,Option.bind_some,ee]
  · rw [ev,dv,cv,bv,av,abcd.keys,abc.keys,ab.keys,as.keys]
    rfl

theorem last_run {s : State} (h : Context s) :
    ∃ t, runBlock isa (flPair 24 ++ six 26) s = some t ∧ Context t ∧ Stable s t ∧
      halves t = lastRounds (keyWord s) (halves s) := by
  obtain ⟨a,ae,ac,as,av⟩ := fl_step h 24 (by decide)
  obtain ⟨b,be,bc,bs,bv⟩ := six_step ac 26 (by decide)
  refine ⟨b,?_,bc,as.trans bs,?_⟩
  · rw [VG.Interleave.runBlock_append,ae,Option.bind_some,be]
  · rw [bv,av,as.keys]
    rfl

end VG.Proof.Camellia.AArch64.Serial

end

end


/-! # The complete 18- or 24-round serial kernel and output whitening -/

@[expose] public section
namespace VG.Proof.Camellia.AArch64.Serial
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Camellia.AArch64.Serial

theorem body_wp {s : State} {R : Nat} (hR : R = 18 ∨ R = 24)
    (hx1 : s.gpr .x1 = BitVec.ofNat 64 R) (hc : Context s)
    (hw0 : InRegions s.wr (s.gpr .x5+BitVec.ofNat 64 768) 8)
    (hw1 : InRegions s.wr (s.gpr .x5+BitVec.ofNat 64 776) 8)
    (m : BitVec 128)
    (initial : halves s = ((m >>> 64).setWidth 64 ^^^ keyWord s 0,m.setWidth 64 ^^^ keyWord s 1)) :
    WP isa cryptBody s fun t =>
      (∀ r, r ∉ written → t.gpr r = s.gpr r) ∧
      Frame [⟨s.gpr .x5+BitVec.ofNat 64 768,16⟩] s.mem t.mem ∧
      Spec.Aes.bytesAt t.mem (s.gpr .x5+BitVec.ofNat 64 768) 16 =
        (Spec.Camellia.encodeBlock (VG.Proof.Camellia.cryptWords (R/6) (keyWord s) m)).toList ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  have finish (u : State) (uc : Context u) (us : Stable s u)
      (hu : halves u = VG.Proof.Camellia.groups (R/6) (keyWord s) (halves s)) :
      WP isa (.block (whitening (8*(R/6)))) u fun t =>
        (∀ r, r ∉ written → t.gpr r = s.gpr r) ∧
        Frame [⟨s.gpr .x5+BitVec.ofNat 64 768,16⟩] s.mem t.mem ∧
        Spec.Aes.bytesAt t.mem (s.gpr .x5+BitVec.ofNat 64 768) 16 =
          (Spec.Camellia.encodeBlock (VG.Proof.Camellia.cryptWords (R/6) (keyWord s) m)).toList ∧
        t.rd = s.rd ∧ t.wr = s.wr := by
    obtain ⟨t,te,to,tg,tf,trd,twr,_⟩ := whitening_run u (8*(R/6))
      (by rcases hR with rfl | rfl <;> decide) uc.read
      (by rw [us.wr,us.regs .x5 (by decide)]; exact hw0)
      (by rw [us.wr,us.regs .x5 (by decide)]; exact hw1)
    refine WP.of_runBlock ⟨t,te,fun r hr => (tg r hr).trans (us.regs r hr),?_,?_,
      trd.trans us.rd,twr.trans us.wr⟩
    · simpa only [us.mem,us.regs .x5 (by decide)] using tf
    · change Spec.Aes.bytesAt t.mem (u.gpr .x5+BitVec.ofNat 64 768) 16 =
        (Spec.Camellia.encodeBlock (((halves u).2 ^^^ keyWord u (8*(R/6))) ++
          ((halves u).1 ^^^ keyWord u (8*(R/6)+1)))).toList at to
      rw [us.regs .x5 (by decide),hu,us.keys,initial] at to
      exact to
  change WP isa (.seq (.block (roundsPrefix ++ [.subImm .x .x8 .x1 18])) _) s _
  refine WP.seq ?_
  rw [WP.block_append_iff]
  obtain ⟨a,ae,ac,as,av⟩ := partial_run hc
  refine WP.of_runBlock ⟨a,ae,?_⟩
  let z := a.write .x .x8 (a.read .x .x1 - BitVec.ofNat 64 18)
  have az : Stable a z := by
    refine ⟨fun r hr => gpr_write_of_ne _ _ _ ?_,rfl,rfl,rfl,rfl⟩
    exact fun h => hr (h ▸ (by decide : Reg.x8 ∈ written))
  have sz := as.trans az
  have zc : Context z := by
    exact ⟨ac.constants,ac.masks.of_regs fun r hr => az.regs r (by revert r; decide),ac.table,
      ac.read_stable az⟩
  have zh : halves z = partialRounds (keyWord s) (halves s) := by
    rw [halves,show z.gpr .x6 = a.gpr .x6 from gpr_write_of_ne _ _ _ (by decide),
      show z.gpr .x7 = a.gpr .x7 from gpr_write_of_ne _ _ _ (by decide)]
    exact av
  refine WP.of_runBlock ⟨z,by
    rw [runBlock_cons,exec_subImm_x (by decide),runStep_some,runBlock_nil],?_⟩
  refine WP.ite (decide (R=18)) ?_ (fun h => ?_) (fun h => ?_)
  · have v : z.gpr .x8 = BitVec.ofNat 64 R - BitVec.ofNat 64 18 := by
      simp only [z,gpr_write_self,State.read,Size.bits,BitVec.setWidth_eq,
        as.regs .x1 (by decide),hx1]
    change some (z.read .x .x8 == 0) = _
    simp only [State.read,Size.bits,BitVec.setWidth_eq,v]
    rcases hR with rfl | rfl <;> decide
  · have he : R = 18 := of_decide_eq_true h
    subst R
    exact finish z zc sz (by rw [zh,partialRounds_eq])
  · have he : R = 24 := by
      have hn : R ≠ 18 := of_decide_eq_false h
      rcases hR with hR | hR
      · exact False.elim (hn hR)
      · exact hR
    subst R
    rw [WP.block_append_iff]
    obtain ⟨b,be,bc,bs,bv⟩ := last_run zc
    refine WP.of_runBlock ⟨b,be,?_⟩
    exact finish b bc (sz.trans bs) (by rw [bv,zh,sz.keys,lastRounds_eq])

end VG.Proof.Camellia.AArch64.Serial

end

end

/-! ### `Camellia.AArch64.Serial.Cipher`, which only this module used -/

section

/-! # Relating the raw memory kernel to the existing public Camellia cipher -/

@[expose] public section
namespace VG.Proof.Camellia.AArch64.Serial
open VG VG.AArch64

theorem cipher_eq_words {s : State} {B : Addr} {k : Nat × List (BitVec 64)}
    (hb : s.gpr .x5 = B) (h : Ready s.mem B k) :
    Spec.Camellia.cipher (Spec.Camellia.subkeysOfWords k.1 k.2)
      (Spec.Aes.bytesAt s.mem (B+BitVec.ofNat 64 768) 16) =
    (Spec.Camellia.encodeBlock (VG.Proof.Camellia.cryptWords (k.1/6) (keyWord s)
      (Spec.Camellia.decodeBlock (Spec.Camellia.blockAt s.mem (B+BitVec.ofNat 64 768))))).toList := by
  rw [VG.Proof.Camellia.cipher_bytes h.rounds]
  apply congrArg (fun x : BitVec 128 => (Spec.Camellia.encodeBlock x).toList)
  apply VG.Proof.Camellia.Serial.cryptWords_congr _ (by rcases h.rounds with hr | hr <;> simp [hr])
  intro i hi
  rw [keyWord,hb,readBE,h.keys i (by simpa only [Spec.Camellia.scheduleLength] using hi)]

end VG.Proof.Camellia.AArch64.Serial

end

end

/-! ### `Camellia.AArch64.Serial.Constants`, which only this module used -/

section

/-! # Loading the public substitution table and rotation masks -/

@[expose] public section
namespace VG.Proof.Camellia.AArch64.Serial
open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl
open VG.Impl.Camellia.AArch64.Serial

theorem quarterConstants_run (s : State) :
    ∃ t, runBlock isa quarterConstants s = some t ∧ Constants t ∧
      (∀ r, r ≠ .x15 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      (∀ v, v ≠ .v4 → v ≠ .v5 → v ≠ .v6 → t.v v = s.v v) :=
  VG.Proof.Sm4.AArch64.Serial.quarterConstants_run s

theorem loadSbox_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .x5) 256)
    (bytes : ∀ k < 256, s.mem (s.gpr .x5 + BitVec.ofNat 64 k) =
      Spec.Camellia.sbox1Table.getD k 0) :
    WP isa (.block loadSbox) s fun t => Table t ∧ t = { s with v := t.v } := by
  refine WP.mono (VG.Proof.Sm4.AArch64.Serial.loads_ok s readable 16 (by decide))
    fun t ⟨ht,_,he⟩ => ⟨?_,he⟩
  intro k hk
  rw [tbyte,ht _ (by omega_using [hk])]
  change (s.mem.read _ 16).extractLsb' (8*(k%16)) 8 = _
  rw [Mem.extractLsb'_read s.mem _ (by omega_using []),VG.Offset.add_add,
    show 16*(k/16)+k%16 = k by omega_using []]
  exact bytes k hk

theorem maskConstants_run (s : State) :
    ∃ t, runBlock isa maskConstants s = some t ∧ Masks t ∧
      (∀ r, r ∉ maskRegs → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  obtain ⟨a,ae,av,ag,am,ard,awr⟩ := VG.Proof.Sm4.AArch64.imm_ok s .x0 keepIn
  obtain ⟨b,be,bv,bg,bm,brd,bwr⟩ := VG.Proof.Sm4.AArch64.imm_ok a .x3 inHigh
  obtain ⟨c,ce,cv,cg,cm,crd,cwr⟩ := VG.Proof.Sm4.AArch64.imm_ok b .x4 inLow
  obtain ⟨d,de,dv,dg,dm,drd,dwr⟩ := VG.Proof.Sm4.AArch64.imm_ok c .x9 keepOut
  obtain ⟨e,ee,ev,eg,em,erd,ewr⟩ := VG.Proof.Sm4.AArch64.imm_ok d .x13 outHigh
  obtain ⟨f,fe,fv,fg,fm,frd,fwr⟩ := VG.Proof.Sm4.AArch64.imm_ok e .x14 outLow
  obtain ⟨t,te,tv,tg,tm,trd,twr⟩ := VG.Proof.Sm4.AArch64.imm_ok f .x15 downLow
  have run : runBlock isa maskConstants s = some t := by
    rw [maskConstants,VG.Interleave.runBlock_append,VG.Interleave.runBlock_append,
      VG.Interleave.runBlock_append,VG.Interleave.runBlock_append,VG.Interleave.runBlock_append,
      VG.Interleave.runBlock_append,ae,Option.bind_some,be,Option.bind_some,ce,Option.bind_some,
      de,Option.bind_some,ee,Option.bind_some,fe,Option.bind_some,te]
  have hsp : t.sp = s.sp := by
    obtain ⟨_,t',hex,rfl⟩ := (WP.of_runBlock ⟨t,run,rfl⟩ : WP isa (.block maskConstants) s (· = t))
    exact Exec.sp hex
  refine ⟨t,run,?_,?_,by rw [tm,fm,em,dm,cm,bm,am],by rw [trd,frd,erd,drd,crd,brd,ard],
    by rw [twr,fwr,ewr,dwr,cwr,bwr,awr],hsp,VG.AArch64.Tbl.runBlock_v (by decide) run⟩
  · refine ⟨?_,?_,?_,?_,?_,?_,tv⟩
    · rw [tg _ (by decide),fg _ (by decide),eg _ (by decide),dg _ (by decide),cg _ (by decide),
        bg _ (by decide),av]
    · rw [tg _ (by decide),fg _ (by decide),eg _ (by decide),dg _ (by decide),cg _ (by decide),bv]
    · rw [tg _ (by decide),fg _ (by decide),eg _ (by decide),dg _ (by decide),cv]
    · rw [tg _ (by decide),fg _ (by decide),eg _ (by decide),dv]
    · rw [tg _ (by decide),fg _ (by decide),ev]
    · rw [tg _ (by decide),fv]
  · intro r hr
    simp only [maskRegs,List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    rw [tg r hr.2.2.2.2.2.2,fg r hr.2.2.2.2.2.1,eg r hr.2.2.2.2.1,dg r hr.2.2.2.1,cg r hr.2.2.1,
      bg r hr.2.1,ag r hr.1]

theorem constants_wp (s : State)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .x5) 256)
    (bytes : ∀ k < 256, s.mem (s.gpr .x5+BitVec.ofNat 64 k) = Spec.Camellia.sbox1Table.getD k 0) :
    WP isa (.block constants) s fun t => Constants t ∧ Masks t ∧ Table t ∧
      (∀ r, r ∉ maskRegs → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  rw [constants,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (loadSbox_ok s readable bytes) fun a ⟨atab,ae⟩ => ?_
  obtain ⟨b,be,bc,bg,bm,brd,bwr,bsp,bvec⟩ := quarterConstants_run a
  refine WP.of_runBlock ⟨b,be,?_⟩
  obtain ⟨c,ce,cmask,cg,cm,crd,cwr,csp,cvec⟩ := maskConstants_run b
  refine WP.of_runBlock ⟨c,ce,?_,cmask,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Constants,cvec] using bc
  · intro j hj
    rw [cvec,tbyte_congr' (fun i hi => by
      have hn := VG.AArch64.Tbl.treg_ne8 i hi
      exact bvec _ hn.2.2.2.2.1 hn.2.2.2.2.2.1 hn.2.2.2.2.2.2.1) j hj]
    exact atab j hj
  · intro r hr
    rw [cg _ hr,bg _ (fun h => hr (by rw [h]; decide)),ae]
  · rw [cm,bm,ae]
  · rw [crd,brd,ae]
  · rw [cwr,bwr,ae]
  · rw [csp,bsp,ae]

end VG.Proof.Camellia.AArch64.Serial

end

end


/-! # The serial Camellia core meets the existing cipher and workspace contract -/

@[expose] public section
namespace VG.Proof.Camellia.AArch64.Serial
open VG VG.AArch64 VG.Impl.Camellia.AArch64.Serial
open VG.Proof.Modes.AArch64 (ScrIn coreRegion bufRegion)

theorem crypt_wp {s : State} {B : Addr} {k : Nat × List (BitVec 64)}
    (hB : s.gpr .x5 = B) (hs : ScrIn s B core.total) (ready : Ready s.mem B k)
    (hx1 : s.gpr .x1 = BitVec.ofNat 64 k.1) :
    WP isa core.crypt s fun t => t.gpr .x5 = B ∧
      t.gpr .x23 = s.gpr .x23 ∧ t.gpr .x24 = s.gpr .x24 ∧
      Ready t.mem B k ∧ t.gpr .x1 = BitVec.ofNat 64 k.1 ∧
      Frame [bufRegion core B] s.mem t.mem ∧
      Spec.Aes.bytesAt t.mem (B+BitVec.ofNat 64 768) 16 =
        Spec.Camellia.cipher (Spec.Camellia.subkeysOfWords k.1 k.2)
          (Spec.Aes.bytesAt s.mem (B+BitVec.ofNat 64 768) 16) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  have readable : InRegions (s.rd ++ s.wr) (s.gpr .x5) 256 := by
    rw [hB]
    exact ⟨_,List.mem_append_right _ hs.wr,by
      change (⟨B,3344⟩ : Region).Contains B 256
      simp [Region.Contains]⟩
  have bytes : ∀ j < 256, s.mem (s.gpr .x5+BitVec.ofNat 64 j) = Spec.Camellia.sbox1Table.getD j 0 := by
    rw [hB]; exact ready.sbox
  change WP isa (.seq (.block (constants ++ loadBlock)) cryptBody) s _
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (constants_wp s readable bytes) fun a ⟨ac,amask,atab,ag,am,ard,awr,_⟩ => ?_
  have abase : a.gpr .x5 = B := (ag _ (by decide)).trans hB
  have ar : ∀ off ∈ [256,264,768,776], InRegions (a.rd ++ a.wr) (a.gpr .x5+BitVec.ofNat 64 off) 8 := by
    intro off hoff
    have bound : off+8 ≤ 3344 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hoff; omega_using [hoff]
    rw [ard,awr,abase]
    exact ⟨_,List.mem_append_right _ hs.wr,VG.Offset.contains_base B bound (by omega_using [bound])⟩
  obtain ⟨c,ce,cv,cg,cm,crd,cwr,_,cvec⟩ := loadBlock_run a ar
  refine WP.of_runBlock ⟨c,ce,?_⟩
  have cbase : c.gpr .x5 = B := (cg _ (by decide)).trans abase
  have cmem : c.mem = s.mem := cm.trans am
  have crd' : c.rd = s.rd := crd.trans ard
  have cwr' : c.wr = s.wr := cwr.trans awr
  have cctx : Context c := by
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [Constants,cvec] using ac
    · exact amask.of_regs fun r hr => cg r (by revert r; decide)
    · simpa only [Table,cvec] using atab
    · intro j hj
      rw [crd',cwr',cbase]
      exact ⟨_,List.mem_append_right _ hs.wr,VG.Offset.contains_base B
        (by omega_using [hj] : 256+8*j+8 ≤ 3344) (by omega_using [hj])⟩
  have cx1 : c.gpr .x1 = BitVec.ofNat 64 k.1 :=
    (cg _ (by decide)).trans ((ag _ (by decide)).trans hx1)
  have ak : keyWord a = keyWord s := by
    funext j
    simp only [keyWord,am,ag .x5 (by decide)]
  have ck : keyWord c = keyWord s := by
    funext j
    simp only [keyWord,cmem,cg .x5 (by decide),ag .x5 (by decide)]
  let m := Spec.Camellia.decodeBlock (Spec.Camellia.blockAt s.mem (B+BitVec.ofNat 64 768))
  have initial : halves c = ((m >>> 64).setWidth 64 ^^^ keyWord c 0,m.setWidth 64 ^^^ keyWord c 1) := by
    rw [cv,ck,ak,am,abase]
    have d := decoded_halves s.mem (B+BitVec.ofNat 64 768)
    rw [VG.Offset.add_add] at d
    rw [show (m >>> 64).setWidth 64 = _ from d.1,show m.setWidth 64 = _ from d.2]
  refine WP.mono (body_wp ready.rounds cx1 cctx
    (by rw [cwr',cbase]; exact ⟨_,hs.wr,VG.Offset.contains_base B (by decide : 768+8 ≤ 3344) (by decide)⟩)
    (by rw [cwr',cbase]; exact ⟨_,hs.wr,VG.Offset.contains_base B (by decide : 776+8 ≤ 3344) (by decide)⟩)
    m initial) fun t ⟨tg,tf,to,trd,twr⟩ => ?_
  have frame : Frame [bufRegion core B] s.mem t.mem := by
    change Frame [⟨B+BitVec.ofNat 64 768,16⟩] s.mem t.mem
    simpa only [cbase,cmem] using tf
  have rt : Ready t.mem B k := ready.frame frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst r
    exact Or.inr (fun _ h => h))
  refine ⟨(tg _ (by decide)).trans cbase,?_,?_,rt,?_,?_,?_,trd.trans crd',twr.trans cwr'⟩
  · exact (tg _ (by decide)).trans ((cg _ (by decide)).trans (ag _ (by decide)))
  · exact (tg _ (by decide)).trans ((cg _ (by decide)).trans (ag _ (by decide)))
  · exact (tg _ (by decide)).trans cx1
  · exact frame
  · rw [cbase,ck] at to
    rw [cipher_eq_words hB ready]
    exact to

end VG.Proof.Camellia.AArch64.Serial

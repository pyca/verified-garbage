module
public import VerifiedGarbage.Impl.AesGcm.X86_64.BoundedGather
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-! The aligned YMM stores cover the same 2672 bytes as the ordinary complete stack wipe.
The replacement restores the same final state. Its access trace depends only on the initial stack pointer. -/
-- separate module: the fixed-frame cleanup proof is independent of the gathered AES-GCM payload.
@[expose] public section
namespace VG.X86_64.Scrub.GatherWipe
open VG.Impl.AesGcm.X86_64.DirectGather
open VG.Impl.AesGcm.X86_64.DirectGather.AlignedWipe
open VG.Impl.Scrub.X86_64 VG.X86_64.Residue

theorem inside {b off w : Nat} (s : State) (hr : ⟨s.gpr .rsp,b⟩ ∈ s.wr) (hb : b < 2^64)
    (h : off+w ≤ b) : InRegions s.wr (s.gpr .rsp + BitVec.ofNat 64 off) w := by
  refine ⟨_,hr,?_⟩
  simp only [Region.Contains]
  rw [show s.gpr .rsp + BitVec.ofNat 64 off - s.gpr .rsp = BitVec.ofNat 64 off by bv_omega,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  exact h
theorem mask_aligned (a : Addr) (k : Nat) (hk : k ≤ 64) :
    a.toNat &&& ((2^(64-k)-1)*2^k) = a.toNat / 2^k * 2^k := by
  let m := (2^(64-k)-1)*2^k
  have hp : 0 < 2^k := Nat.two_pow_pos _
  have hm : m / 2^k = 2^(64-k)-1 := Nat.mul_div_cancel _ hp
  have hn : m % 2^k = 0 := by simp [m]
  have q : a.toNat / 2^k < 2^(64-k) := by
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    rw [←Nat.pow_add, Nat.sub_add_cancel hk]
    exact a.isLt
  have dv := Nat.and_div_two_pow (a:=a.toNat) (b:=m) (n:=k)
  have md := Nat.and_mod_two_pow (a:=a.toNat) (b:=m) (n:=k)
  rw [hm, Nat.and_two_pow_sub_one_of_lt_two_pow q] at dv
  rw [hn,Nat.and_zero] at md
  calc
    _ = (a.toNat &&& m) / 2^k * 2^k + (a.toNat &&& m) % 2^k := by
      rw [Nat.mul_comm ((a.toNat &&& m) / 2^k), Nat.div_add_mod]
    _ = _ := by rw [dv,md,Nat.add_zero]

def ptr (sp : Addr) (w : Nat) := (sp+BitVec.ofNat 64 w) &&& -BitVec.ofNat 64 w
def delta (sp : Addr) (w : Nat) := w-sp.toNat%w
theorem ptr_eq (sp : Addr) :
    ptr sp 32 = sp+BitVec.ofNat 64 (delta sp 32) := by
  apply BitVec.eq_of_toNat_eq
  have h := mask_aligned (sp+32) 5 (by decide)
  simp only [ptr,BitVec.toNat_and,delta,BitVec.toNat_add,BitVec.toNat_ofNat,Nat.reducePow] at *
  change (sp.toNat+32)%18446744073709551616 &&& 18446744073709551584 = _
  change (sp.toNat+32)%18446744073709551616 &&& 18446744073709551584 = _ at h
  rw [h]
  change ((sp.toNat + 32) % 18446744073709551616) / 32 * 32 = (sp.toNat+((32-sp.toNat%32)%18446744073709551616))%18446744073709551616
  omega
/-- Each offset denotes one store of 32 bytes, relative to the bottom of the 2664-byte frame. -/
def plan (sp : Addr) : List Nat :=
 let w := 32
 let d := delta sp w
 [0] ++ (List.range 82).map (fun i => d+32*i) ++ [82*w,2664-w]

theorem covers (sp : Addr) (i : Nat) :
    (∃ off ∈ plan sp, off ≤ i ∧ i < off+32) ↔ i < 2664 := by
  let d := delta sp 32
  have dw : d ≤ 32 := Nat.sub_le _ _
  have interior (hd : d ≤ i) (he : i < 82 * 32) :
      ∃ off ∈ plan sp, off ≤ i ∧ i < off+32 := by
    let n := (i-d)/32
    have hn : n < 82 := by
      dsimp [n] at *; omega
    refine ⟨d+32*n,?_,?_⟩
    · simp only [plan,List.mem_append,List.mem_map,List.mem_range,List.mem_cons,List.not_mem_nil]
      exact Or.inl (Or.inr ⟨n,hn,rfl⟩)
    · dsimp [n] at *; omega
  constructor
  · rintro ⟨off,member,lb,ub⟩
    simp only [plan,List.mem_append,List.mem_map,List.mem_range,List.mem_cons,List.not_mem_nil] at member
    rcases member with ((e|h)|⟨n,hn,en⟩)|(e|e|h)
    · subst off; omega
    · exact h.elim
    · change d+32*n=off at en
      omega
    · subst off; omega
    · subst off; omega
    · exact h.elim
  · intro hi
    by_cases hf : i < 32
    · exact ⟨0,by simp [plan],by omega⟩
    by_cases hb : i < 82*32
    · exact interior (by omega) hb
    by_cases hl : 2664-32 ≤ i
    · exact ⟨2664-32,by simp [plan],hl,by omega⟩
    exact ⟨82*32,by simp [plan],by omega,by omega⟩

def locOff (d : Nat) (l : Loc) := (if l.1 then d else 0) + l.2
theorem plan_map (sp : Addr) :
    locs.map (locOff (delta sp 32)) = plan sp := by
  simp [locs,locOff,plan,List.map_append,List.map_map,Function.comp_def]
theorem ea_loc (l : Loc) (s : State) (d : Nat)
    (h : s.gpr .r11 = s.gpr .rsp + BitVec.ofNat 64 d) :
    s.ea {base := locReg l,disp := (l.2 : Int)} = s.gpr .rsp + BitVec.ofNat 64 (locOff d l) := by
  rcases l with ⟨b,n⟩
  cases b <;> simp [locReg,locOff,State.ea,BitVec.ofInt_natCast,h,BitVec.ofNat_add,BitVec.add_assoc]

def locAddr (sp : Addr) (d : Nat) (l : Loc) := sp + BitVec.ofNat 64 (locOff d l)
def locTrace (sp : Addr) (d : Nat) (ls : List Loc) := ls.map fun l => Leak.addr (locAddr sp d l)

theorem stores_ok (d : Nat) (ls : List Loc) (s : State)
    (frame : ⟨s.gpr .rsp,2664⟩ ∈ s.wr) (r : s.gpr .r11 = s.gpr .rsp+BitVec.ofNat 64 d)
    (hy : s.ymm .xmm0=0)
    (inside : ∀ l ∈ ls, locOff d l + 32 ≤ 2664) :
    ∃ m, execBlock isa (ls.map emitStore) s =
       some ({s with mem:=m},locTrace (s.gpr .rsp) d ls) ∧
      ∀ x, m x = if ∃ l ∈ ls, locOff d l ≤ (x-s.gpr .rsp).toNat ∧
          (x-s.gpr .rsp).toNat < locOff d l + 32 then 0 else s.mem x := by
  induction ls generalizing s with
  | nil => exact ⟨s.mem,rfl,by simp⟩
  | cons l ls ih =>
    let o := locOff d l
    let a := locAddr (s.gpr .rsp) d l
    let m₁ := s.mem.writeW a (0 : BitVec 256)
    let u := {s with mem:=m₁}
    have hi := inside l (List.mem_cons_self ..)
    have perm := GatherWipe.inside (off:=o) (w:=32) s frame (by decide) hi
    have ea := ea_loc l s d r
    have step : VG.X86_64.exec (emitStore l) s = some u := by
      simp [emitStore,reduceExec,State.store256,ea,hy,
        o,a,locAddr,u,m₁] at perm ⊢ <;> exact perm
    have trace : VG.X86_64.addrs (emitStore l) s = [a] := by
      simp [emitStore,addrs,ea,a,locAddr]
    obtain ⟨m,run,read⟩ := ih u frame r hy (fun k hk => inside k (List.mem_cons_of_mem _ hk))
    refine ⟨m,?_,?_⟩
    · simp only [List.map_cons,execBlock,step,trace,run,Option.map_some,List.map_nil,List.nil_append,List.cons_append,locTrace]
      rfl
    · intro x
      have h0 : o+32 < 2^64 := by omega
      have first : m₁ x = if o ≤ (x-s.gpr .rsp).toNat ∧ (x-s.gpr .rsp).toNat < o+32 then 0 else s.mem x := by
        exact (writeW_zero256 ..).trans (ite_cond_congr (propext (off_lt x (s.gpr .rsp) o 32 h0)))
      rw [read]; change (if _ then _ else m₁ x) = _
      rw [first]
      let P := fun k => locOff d k ≤ (x-s.gpr .rsp).toNat ∧ (x-s.gpr .rsp).toNat < locOff d k + 32
      change (if ∃ k ∈ ls, P k then 0 else if P l then 0 else s.mem x) = (if ∃ k ∈ l::ls, P k then 0 else s.mem x)
      have heq : (∃ k ∈ l::ls, P k) ↔ P l ∨ ∃ k ∈ ls, P k := by
        constructor
        · rintro ⟨k,hk,hp⟩; rcases List.mem_cons.mp hk with h|h
          · subst k; exact Or.inl hp
          · exact Or.inr ⟨k,h,hp⟩
        · rintro (h|⟨k,hk,hp⟩)
          · exact ⟨_,List.mem_cons_self ..,h⟩
          · exact ⟨k,List.mem_cons_of_mem _ hk,hp⟩
      by_cases h1 : P l <;> by_cases h2 : ∃ k ∈ ls, P k <;> simp only [heq,h1,h2,or_true,or_false,↓reduceIte]

def afterSetup (s : State) : State :=
 let p := ptr (s.gpr .rsp) 32
 (arithFlags s p false false).setReg .r11 p

theorem setup_ok (s : State) : execBlock isa setup s = some (afterSetup s, []) := by
  simp [setup,execBlock,isa,reduceExec,execAlu,readSrc,addrs,srcAddrs,State.setReg,
    arithFlags,State.setFlags,afterSetup,ptr] <;> funext i <;> by_cases hi : i = .r11 <;> simp [hi]

def alignedTr (sp : Addr) := locTrace sp (delta sp 32) locs
def zeroFlags (s : State) := s.cf=some false ∧ s.of=some false ∧ s.zf=some true ∧ s.sf=some false

theorem chunk_ok (s : State) (frame : ⟨s.gpr .rsp,2664⟩ ∈ s.wr)
    (hy : s.ymm .xmm0=0) (hr : s.gpr .r11=0) (hf : zeroFlags s) :
     ∃ m, execBlock isa code s = some ({s with mem:=m}, alignedTr (s.gpr .rsp)) ∧
       ∀ x, m x = if (x-s.gpr .rsp).toNat < 2664 then 0 else s.mem x := by
  let d := delta (s.gpr .rsp) 32
  let t := afterSetup s
  have rsp : t.gpr .rsp = s.gpr .rsp := rfl
  have r : t.gpr .r11 = t.gpr .rsp + BitVec.ofNat 64 d := ptr_eq (s.gpr .rsp)
  have bounds (l) (hl : l ∈ locs) : locOff d l+32 ≤ 2664 := by
    have hm : locOff d l ∈ plan (s.gpr .rsp) := by rw [←plan_map]; exact List.mem_map_of_mem hl
    have hp : 32 > 0 := by decide
    have cov := (covers (s.gpr .rsp) (locOff d l + 32 - 1)).mp ⟨_,hm,by omega,by omega⟩
    omega
  obtain ⟨m,run,read⟩ := stores_ok d locs t frame r hy bounds
  refine ⟨m,?_,?_⟩
  · have restore := execBlock_gprs [.r11] (by decide) ({t with mem:=m})
    have eq : clearedG [.r11] {t with mem:=m} = {s with mem:=m} := by
      rcases hf with ⟨hc,ho,hz,hs⟩
      simp only [clearedG,t, afterSetup,State.setReg,arithFlags,State.setFlags,List.mem_singleton,State.mk.injEq,
        hc,ho,hz,hs,and_true]
      funext i; by_cases hi : i = .r11 <;> simp [hi,hr]
    rw [eq] at restore
    change execBlock isa [zeroR .r11] _ = _ at restore
    dsimp only [t] at run restore
    exact (by
      rw [code,execBlock_append,execBlock_append,setup_ok]
      simp only [Option.bind_some,run,restore,Option.map_some, List.nil_append,List.append_nil]
      rfl)
  · intro x
    rw [read]
    apply ite_cond_congr
    apply propext
    rw [← covers (s.gpr .rsp) _, ← plan_map]
    rw [rsp]
    constructor
    · rintro ⟨l,hl,h⟩; exact ⟨_,List.mem_map_of_mem hl,h⟩
    · rintro ⟨o,hm,h⟩; obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hm; exact ⟨l,hl,h⟩

abbrev ks := wipeKs [8,2664]
theorem inner_covered {i : Nat} (hi : i<2664) : CCov ks 0 2664 i := by
  refine ⟨hi,?_⟩
  have hh : ∀ b ∈ [8,2664], b % 8 = 0 := by intro b hb; simp at hb; rcases hb with e|e <;> subst b <;> decide
  have c := cov_all [8,2664] hh i (by simpa using Nat.lt_trans hi (show 2664<8+2664 by decide))
  change (if i < 2664 then (if i < 0 then false else decide (i-0<2664) && covC ks 0 2664 (i-0)) else _) = true at c
  simpa only [hi,↓reduceIte,Nat.not_lt_zero,Nat.sub_zero,decide_true,Bool.true_and] using c

def pushed (s : State) (n : Nat) : State :=
 {s.setReg .rsp (s.gpr .rsp-BitVec.ofNat 64 n) with wr := ⟨s.gpr .rsp-BitVec.ofNat 64 n,n⟩ :: s.wr}
theorem push_view {n : Nat} {s u : State} (h : isa.push (.alloc n) s = some u) :
    u = {s.setReg .rsp (s.gpr .rsp-BitVec.ofNat 64 n) with
      wr := ⟨s.gpr .rsp-BitVec.ofNat 64 n,n⟩ :: s.wr} := by
  change push (.alloc n) s = some u at h; simp only [push] at h
  split at h <;> simp_all
theorem top_run {s : State} (hr : ⟨s.gpr .rsp,8⟩ ∈ s.wr) :
  execBlock isa save8 s = some ({s with mem:=s.mem.writeW (s.gpr .rsp) (s.gpr .r11)},[.addr (s.gpr .rsp)]) := by
  have h8 : InRegions s.wr (s.gpr .rsp) 8 := by refine ⟨_,hr,?_⟩; simp [Region.Contains]
  simp [save8,execBlock,isa,reduceExec,addrs,State.store64,State.ea,h8]
def start (s : State) := clearedG [.r11] (clearedH .evex (clearedV .evex xregs s))
theorem enterWipe (s : State) : execBlock isa preCode s = some (start s,[]) := by
  rw [show preCode = (xregs.map (zeroX .evex) ++ clearHigh .evex) ++ [Reg.r11].map zeroR from rfl,
    execBlock_append,execBlock_append,execBlock_vecs]
  simp only [Option.bind_some,execBlock_high,Option.map_some,List.nil_append]
  rw [execBlock_gprs _ (by decide)]
  rfl
theorem chunk_agrees (s : State) (hr : ⟨s.gpr .rsp,2664⟩ ∈ s.wr)
    (hx : s.xmm .xmm0=0) (hh : s.ymmHi .xmm0=0) (hg : s.gpr .r11=0) (hf : zeroFlags s) :
    ∃ t, execBlock isa (chunkStores true ks 0 2664) s = some (t,chunkTr true ks 0 (s.gpr .rsp) 2664) ∧
      execBlock isa code s = some (t,alignedTr (s.gpr .rsp)) := by
  obtain ⟨m,hn,hzero,hrest⟩ := chunk_run true ks 0 2664 (by decide) (by decide) s hr
    (fun _ => hx) (fun _ _ => hh) (fun _ => hg)
  have hy : s.ymm .xmm0=0 := by simp [State.ymm,hx,hh]
  obtain ⟨m',hw,hread⟩ := chunk_ok s hr hy hg hf
  have eq : m' = m := by
    funext x
    rw [hread]
    split
    · rename_i h; exact (hzero x (inner_covered h)).symm
    · rename_i h; exact (hrest x (fun f => h f.1)).symm
  subst m'
  exact ⟨_,hn,hw⟩
def wipeTrace (sp : Addr) := [.addr (sp-8)] ++ alignedTr (sp-8-2664)
theorem wipe_refines {s t : State} {oldTr : List Leak}
    (run : Exec isa (wipe true ks [8,2664]) s oldTr t) (hx : s.xmm .xmm0=0)
    (hh : s.ymmHi .xmm0=0) (hg : s.gpr .r11=0) (hf : zeroFlags s) :
    Exec isa wipeWhole s (wipeTrace (s.gpr .rsp)) t := by
  change Exec isa (.frame (.alloc 8) (.seq (.block save8)
    (.frame (.alloc 2664) (.seq (.block (chunkStores true ks 0 2664)) (.block [])) (.free 2664))) (.free 8)) s oldTr t at run
  cases run with
  | @frame _ _ _ _ outer _ _ _ hp body hpop =>
   cases body with
   | @seq _ _ _ after _ _ _ top nested =>
    cases top with
    | block top =>
     cases nested with
     | @frame _ _ _ _ inner _ _ _ hp2 middle hpop2 =>
      cases middle with
      | seq stored empty =>
       cases stored with
       | block stored =>
        cases empty with
        | block empty =>
         simp only [execBlock, Option.some.injEq,Prod.mk.injEq] at empty
         obtain ⟨rfl,rfl⟩ := empty
         have view : outer = GatherWipe.pushed s 8 := push_view hp
         have ho : outer.gpr .rsp=s.gpr .rsp-8 := by rw [view]; simp [GatherWipe.pushed,State.setReg]
         have topmem := top_run (s := outer) (by rw [view]; simp [GatherWipe.pushed,State.setReg])
         rw [topmem, Option.some.injEq,Prod.mk.injEq] at top
         obtain ⟨hAfter,rfl⟩ := top
         have vi : inner = GatherWipe.pushed after 2664 := push_view hp2
         have regs : inner.gpr .rsp=(s.gpr .rsp-8)-2664 := by rw [vi,←hAfter]; simp [GatherWipe.pushed,State.setReg,ho]
         have hx' : inner.xmm .xmm0=0 := by rw [vi,←hAfter,view]; exact hx
         have hh' : inner.ymmHi .xmm0=0 := by rw [vi,←hAfter,view]; exact hh
         have hg' : inner.gpr .r11=0 := by rw [vi,←hAfter,view]; exact hg
         have hf' : zeroFlags inner := by rw [vi,←hAfter,view]; exact hf
         obtain ⟨_,orig,repl⟩ := chunk_agrees inner (by rw [vi]; simp [GatherWipe.pushed,State.setReg]) hx' hh' hg' hf'
         rw [orig,Option.some.injEq,Prod.mk.injEq] at stored
         obtain ⟨rfl,rfl⟩ := stored
         rw [hAfter] at topmem
         have out := Exec.frame hp (Exec.seq (Exec.block topmem)
           (Exec.frame hp2 (Exec.block repl) hpop2)) hpop
         simpa only [wipeWhole,wipeTrace,isa,addrs,List.map_nil,List.nil_append,List.append_nil,
           ho,regs,List.append_assoc] using out
theorem tail_refines {s t : State} {l : List Leak}
    (run : Exec isa (scrubTail .evex 0 xregs (psOf ks) (gsAll ks) ks [8,2664] .avx) s l t) :
    Exec isa (AlignedWipe.tail ) s (wipeTrace (s.gpr .rsp)) t := by
  change Exec isa (.seq (.block preCode) (.seq (.block []) (.seq (wipe true ks [8,2664]) (.block postCode)))) s l t at run
  cases run with
  | seq pre rest =>
   cases pre with
   | block pre =>
    rw [enterWipe,Option.some.injEq,Prod.mk.injEq] at pre
    obtain ⟨rfl,rfl⟩ := pre
    cases rest with
    | seq mx rest =>
     cases mx with
     | block mx =>
      simp only [execBlock,Option.some.injEq,Prod.mk.injEq] at mx
      obtain ⟨rfl,rfl⟩ := mx
      cases rest with
      | @seq _ _ _ u _ _ _ wipe post =>
       cases post with
       | block post =>
        have clear := execBlock_clearGpr 0 postRegs (by decide) (by decide) u
        change execBlock isa postCode u = _ at post
        change execBlock isa postCode u = _ at clear
        rw [clear,Option.some.injEq,Prod.mk.injEq] at post
        obtain ⟨rfl,rfl⟩ := post
        have wiped :=  wipe_refines wipe (hx:=by rfl) (hh:=by rfl) (hg:=by rfl) (hf:=by exact ⟨rfl,rfl,rfl,rfl⟩)
        have ee : Exec isa (.block []) (start s) [] (start s) := .block rfl
        have run' := Exec.seq (Exec.block (enterWipe s)) (Exec.seq ee (Exec.seq wiped (Exec.block clear)))
        simpa only [AlignedWipe.tail,mxFix,List.nil_append,List.append_nil,show (start s).gpr .rsp=s.gpr .rsp by rfl] using run'
theorem complete_refines {c : Prog isa} (safe : SpSafe c) {s t : State} {o : List Leak}
    (old : Exec isa (scrubAll .evex 0 2672 c) s o t) :
    ∃ l u, Exec isa c s l u ∧ Exec isa (AlignedWipe.scrub c) s (l ++ wipeTrace (s.gpr .rsp)) t := by
  change Exec isa (.seq c (scrubTail .evex 0 xregs (psOf ks) (gsAll ks) ks [8,2664] .avx)) s o t at old
  cases old with
  | seq core tail =>
    exact ⟨_,_,core,by simpa only [AlignedWipe.scrub,Exec.rsp safe core] using Exec.seq core (tail_refines tail)⟩
/-- Changes only the proven epilogue of an already verified function. -/
theorem verified {c : Prog isa} {k : Contract isa} (safe : SpSafe c)
    (hp : ∀ s t : State, k.pub s t → s.gpr .rsp=t.gpr .rsp)
    (ct : ConstantTime isa k.pre k.pub c)
    (old : VerifiedScrubbed target (scrubAll .evex 0 2672 c) k 0) :
    VerifiedScrubbed target (AlignedWipe.scrub c) k 0 := by
  have simulate {s : State} {n : List Leak} {v : State} (hs : k.pre s) (e : Exec isa (AlignedWipe.scrub c) s n v) :
      ∃ o l u, Exec isa (scrubAll .evex 0 2672 c) s o v ∧ Exec isa c s l u ∧ n=l++wipeTrace (s.gpr .rsp) := by
    obtain ⟨o,w,original,_,_⟩ := old.verified.1 s hs
    obtain ⟨l,u,raw,new⟩ := complete_refines safe original
    obtain ⟨ht,hs'⟩ := Exec.det e new
    subst w
    exact ⟨o,l,u,original,raw,ht⟩
  refine ⟨⟨?_,?_,old.verified.2.2⟩,?_,?_⟩
  · intro s hs
    obtain ⟨o,v,original,abi,post⟩ := old.verified.1 s hs
    obtain ⟨l,u,_,new⟩ := complete_refines safe original
    exact ⟨_,_,new,abi,post⟩
  · intro a b i j u v ha hb pub aRun bRun
    obtain ⟨_,_,_,_,ea,et⟩ := simulate ha aRun
    obtain ⟨_,_,_,_,eb,ft⟩ := simulate hb bRun
    rw [et,ft,ct _ _ _ _ _ _ ha hb pub ea eb,hp _ _ pub]
  · intro a b i j u v ha hb pub before unk aRun bRun
    obtain ⟨_,_,_,ea,_,_⟩ := simulate ha aRun
    obtain ⟨_,_,_,eb,_,_⟩ := simulate hb bRun
    exact old.noResidue _ _ _ _ _ _ ha hb pub before unk ea eb
  · intro ty f hy hf a l b ha ab
    obtain ⟨_,_,_,orig,_,_⟩ := simulate ha ab
    exact old.retAbi ty f hy hf _ _ _ ha orig
theorem spSafe {c : Prog isa} (h : c.all (fun i => !isa.writesSp i) = true) :
    (AlignedWipe.scrub c).all (fun i => !isa.writesSp i) = true :=
  Bool.and_eq_true_iff.mpr ⟨h, by decide⟩

end VG.X86_64.Scrub.GatherWipe

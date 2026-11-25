// The functions of `src/internal/vg_dsa_probable_prime_adx.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_probable_prime_adx:
	lea rsp, [rsp-56]
	mov QWORD PTR [rsp], rbx
	mov QWORD PTR [rsp+8], rbp
	mov QWORD PTR [rsp+16], r12
	mov QWORD PTR [rsp+24], r13
	mov QWORD PTR [rsp+32], r14
	mov QWORD PTR [rsp+40], r15
	mov QWORD PTR [rsp+48], r8
	mov r8, r9
	mov r9, rdx
	mov rsi, rdi
	add rdi, 28672
	mov r12, r8
	shr r12, 6
	mov eax, 4
	cmp r8, 257
	cmovb r12, rax
	mov QWORD PTR [rdi+48], r12
	mov eax, 0
	mov QWORD PTR [rdi+56], rax
	mov rax, r12
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rdx, rdi
	add rdx, 256
	mov QWORD PTR [rdi+64], rdx
	add rdx, rax
	mov QWORD PTR [rdi+72], rdx
	add rdx, rax
	mov QWORD PTR [rdi+80], rdx
	add rdx, rax
	mov QWORD PTR [rdi+88], rdx
	add rdx, rax
	mov QWORD PTR [rdi+96], rdx
	add rdx, rax
	mov QWORD PTR [rdi+104], rdx
	add rdx, rax
	mov QWORD PTR [rdi+112], rdx
	add rdx, rax
	mov QWORD PTR [rdi+120], rdx
	add rdx, rax
	mov rax, r12
	add rax, 2
	shl rax, 3
	mov QWORD PTR [rdi+224], rax
	mov rax, rsi
	add rax, 26624
	mov QWORD PTR [rdi+128], rax
	mov rdx, r8
	shr rdx, 3
	mov rax, rdx
	mov r10d, 24
	cmp r8, 160
	cmove rax, r10
	mov QWORD PTR [rdi+136], rax
	mov QWORD PTR [rdi+144], rdx
	mov eax, 64
	mov edx, 128
	cmp r8, 2049
	cmovae rax, rdx
	mov QWORD PTR [rdi+152], rax
	mov eax, 25472
	mov edx, 25408
	cmp r8, 257
	cmovb rax, rdx
	mov rdx, rsi
	add rdx, rax
	mov QWORD PTR [rdi+160], rdx
	mov QWORD PTR [rdi+184], r9
	mov QWORD PTR [rdi+192], rcx
	mov eax, 0
	mov QWORD PTR [rdi+200], rax
	mov r8, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
20:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 20b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rsi, QWORD PTR [rdi+160]
	mov rcx, QWORD PTR [rdi+144]
	mov rbx, QWORD PTR [rdi+64]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
21:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 22f
	jmp 23f
22:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
23:
	test rdx, rdx
	jne 21b
	mov rax, QWORD PTR [rdi+48]
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rbx, QWORD PTR [rdi+120]
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	movabs rax, 3096254808915971
	mov QWORD PTR [rbx], rax
	movabs rax, 6474006069837837
	mov QWORD PTR [rbx+8], rax
	movabs rax, 11540632960958493
	mov QWORD PTR [rbx+16], rax
	movabs rax, 16607251262275627
	mov QWORD PTR [rbx+24], rax
	movabs rax, 20547978246946877
	mov QWORD PTR [rbx+32], rax
	movabs rax, 27303454998462543
	mov QWORD PTR [rbx+40], rax
	movabs rax, 30681232029712485
	mov QWORD PTR [rbx+48], rax
	movabs rax, 38562634458398833
	mov QWORD PTR [rbx+56], rax
	movabs rax, 44192219893399691
	mov QWORD PTR [rbx+64], rax
	movabs rax, 50384763871494307
	mov QWORD PTR [rbx+72], rax
	movabs rax, 55451399353204917
	mov QWORD PTR [rbx+80], rax
	movabs rax, 63895777504854215
	mov QWORD PTR [rbx+88], rax
	movabs rax, 67836495899721957
	mov QWORD PTR [rbx+96], rax
	movabs rax, 75717898328408315
	mov QWORD PTR [rbx+104], rax
	movabs rax, 79658625313079567
	mov QWORD PTR [rbx+112], rax
	movabs rax, 88103003465384229
	mov QWORD PTR [rbx+120], rax
	movabs rax, 97673264344269117
	mov QWORD PTR [rbx+128], rax
	movabs rax, 103302858369204573
	mov QWORD PTR [rbx+136], rax
	movabs rax, 109495410937758069
	mov QWORD PTR [rbx+144], rax
	movabs rax, 117939771909669261
	mov QWORD PTR [rbx+152], rax
	movabs rax, 123569374525063589
	mov QWORD PTR [rbx+160], rax
	movabs rax, 129761927093092795
	mov QWORD PTR [rbx+168], rax
	movabs rax, 137080370978030031
	mov QWORD PTR [rbx+176], rax
	movabs rax, 143272923546976747
	mov QWORD PTR [rbx+184], rax
	movabs rax, 153969135872311817
	mov QWORD PTR [rbx+192], rax
	movabs rax, 160724655575073325
	mov QWORD PTR [rbx+200], rax
	movabs rax, 168606058003759681
	mov QWORD PTR [rbx+208], rax
	movabs rax, 173672693485208153
	mov QWORD PTR [rbx+216], rax
	movabs rax, 180991163140342379
	mov QWORD PTR [rbx+224], rax
	movabs rax, 186057790031987335
	mov QWORD PTR [rbx+232], rax
	movabs rax, 194502142414095009
	mov QWORD PTR [rbx+240], rax
	movabs rax, 204635396196598461
	mov QWORD PTR [rbx+248], rax
	movabs rax, 211390898718835421
	mov QWORD PTR [rbx+256], rax
	movabs rax, 217583459877061365
	mov QWORD PTR [rbx+264], rax
	movabs rax, 228279680793117459
	mov QWORD PTR [rbx+272], rax
	movabs rax, 233346307685024565
	mov QWORD PTR [rbx+280], rax
	movabs rax, 241790685837329223
	mov QWORD PTR [rbx+288], rax
	movabs rax, 248546188359172959
	mov QWORD PTR [rbx+296], rax
	movabs rax, 258679416371741559
	mov QWORD PTR [rbx+304], rax
	movabs rax, 266560844570624929
	mov QWORD PTR [rbx+312], rax
	movabs rax, 275005222722929593
	mov QWORD PTR [rbx+320], rax
	movabs rax, 284012533648393175
	mov QWORD PTR [rbx+328], rax
	movabs rax, 290205086217077749
	mov QWORD PTR [rbx+336], rax
	movabs rax, 295834706011685897
	mov QWORD PTR [rbx+344], rax
	movabs rax, 305967891074188325
	mov QWORD PTR [rbx+352], rax
	movabs rax, 310471610962609219
	mov QWORD PTR [rbx+360], rax
	movabs rax, 317790072027808853
	mov QWORD PTR [rbx+368], rax
	movabs rax, 329612192850707583
	mov QWORD PTR [rbx+376], rax
	movabs rax, 338056571003274397
	mov QWORD PTR [rbx+384], rax
	movabs rax, 345937999202157757
	mov QWORD PTR [rbx+392], rax
	movabs rax, 354382360173937871
	mov QWORD PTR [rbx+400], rax
	movabs rax, 362826755506898173
	mov QWORD PTR [rbx+408], rax
	movabs rax, 366767482491438347
	mov QWORD PTR [rbx+416], rax
	movabs rax, 373522967833281819
	mov QWORD PTR [rbx+424], rax
	movabs rax, 388722839917102417
	mov QWORD PTR [rbx+432], rax
	movabs rax, 401670903596909943
	mov QWORD PTR [rbx+440], rax
	movabs rax, 407300471852172693
	mov QWORD PTR [rbx+448], rax
	movabs rax, 414055957193885099
	mov QWORD PTR [rbx+456], rax
	movabs rax, 419122627035727305
	mov QWORD PTR [rbx+464], rax
	movabs rax, 428692879324153301
	mov QWORD PTR [rbx+472], rax
	movabs rax, 437137291837113851
	mov QWORD PTR [rbx+480], rax
	movabs rax, 444455735722444311
	mov QWORD PTR [rbx+488], rax
	movabs rax, 452337163921327663
	mov QWORD PTR [rbx+496], rax
	movabs rax, 456277890905736777
	mov QWORD PTR [rbx+504], rax
	movabs rax, 468100003137914459
	mov QWORD PTR [rbx+512], rax
	movabs rax, 477670306966996611
	mov QWORD PTR [rbx+520], rax
	movabs rax, 484988776623179427
	mov QWORD PTR [rbx+528], rax
	movabs rax, 493433137595745989
	mov QWORD PTR [rbx+536], rax
	movabs rax, 503003441425090271
	mov QWORD PTR [rbx+544], rax
	movabs rax, 513136660847331069
	mov QWORD PTR [rbx+552], rax
	movabs rax, 525521774573979431
	mov QWORD PTR [rbx+560], rax
	movabs rax, 528899543015688015
	mov QWORD PTR [rbx+568], rax
	movabs rax, 538469821074704225
	mov QWORD PTR [rbx+576], rax
	movabs rax, 549166050580432779
	mov QWORD PTR [rbx+584], rax
	movabs rax, 560988162814052277
	mov QWORD PTR [rbx+592], rax
	movabs rax, 566054781115631565
	mov QWORD PTR [rbx+600], rax
	movabs rax, 573936192134514657
	mov QWORD PTR [rbx+608], rax
	movabs rax, 585758312957413381
	mov QWORD PTR [rbx+616], rax
	movabs rax, 590824948439124003
	mov QWORD PTR [rbx+624], rax
	movabs rax, 599832319494260799
	mov QWORD PTR [rbx+632], rax
	movabs rax, 606024829113272409
	mov QWORD PTR [rbx+640], rax
	movabs rax, 621224735556175985
	mov QWORD PTR [rbx+648], rax
	movabs rax, 630232080842557605
	mov QWORD PTR [rbx+656], rax
	movabs rax, 638676458994862275
	mov QWORD PTR [rbx+664], rax
	movabs rax, 645431944337230049
	mov QWORD PTR [rbx+672], rax
	movabs rax, 656691046486706425
	mov QWORD PTR [rbx+680], rax
	movabs rax, 661757750688418083
	mov QWORD PTR [rbx+688], rax
	movabs rax, 670202128840722741
	mov QWORD PTR [rbx+696], rax
	movabs rax, 675268747142170959
	mov QWORD PTR [rbx+704], rax
	movabs rax, 685964925108029803
	mov QWORD PTR [rbx+712], rax
	movabs rax, 694409329030138249
	mov QWORD PTR [rbx+720], rax
	movabs rax, 709609166753040809
	mov QWORD PTR [rbx+728], rax
	movabs rax, 717490637903694307
	mov QWORD PTR [rbx+736], rax
	movabs rax, 729312741545544183
	mov QWORD PTR [rbx+744], rax
	movabs rax, 737757154059029025
	mov QWORD PTR [rbx+752], rax
	movabs rax, 748453374975216201
	mov QWORD PTR [rbx+760], rax
	movabs rax, 755208860317190759
	mov QWORD PTR [rbx+768], rax
	movabs rax, 759712528665217663
	mov QWORD PTR [rbx+776], rax
	movabs rax, 765342114100218515
	mov QWORD PTR [rbx+784], rax
	movabs rax, 773786483661933225
	mov QWORD PTR [rbx+792], rax
	movabs rax, 785045637351541441
	mov QWORD PTR [rbx+800], rax
	movabs rax, 788986390106671847
	mov QWORD PTR [rbx+808], rax
	movabs rax, 800245543796280067
	mov QWORD PTR [rbx+816], rax
	movabs rax, 810378746038651683
	mov QWORD PTR [rbx+824], rax
	movabs rax, 818823175731219271
	mov QWORD PTR [rbx+832], rax
	movabs rax, 831208229327276901
	mov QWORD PTR [rbx+840], rax
	movabs rax, 836274907759446925
	mov QWORD PTR [rbx+848], rax
	movabs rax, 849785887032675255
	mov QWORD PTR [rbx+856], rax
	movabs rax, 858230265185373135
	mov QWORD PTR [rbx+864], rax
	movabs rax, 867800577604258805
	mov QWORD PTR [rbx+872], rax
	movabs rax, 878496798520708113
	mov QWORD PTR [rbx+880], rax
	movabs rax, 892007803564788801
	mov QWORD PTR [rbx+888], rax
	movabs rax, 901578055853739117
	mov QWORD PTR [rbx+896], rax
	movabs rax, 908896534099201161
	mov QWORD PTR [rbx+904], rax
	movabs rax, 917340938021702835
	mov QWORD PTR [rbx+912], rax
	movabs rax, 930851925885390023
	mov QWORD PTR [rbx+920], rax
	movabs rax, 937044469863615729
	mov QWORD PTR [rbx+928], rax
	movabs rax, 945488822245723395
	mov QWORD PTR [rbx+936], rax
	movabs rax, 953933183218027809
	mov QWORD PTR [rbx+944], rax
	movabs rax, 966318253994347839
	mov QWORD PTR [rbx+952], rax
	movabs rax, 974762709457374585
	mov QWORD PTR [rbx+960], rax
	movabs rax, 984895937468763531
	mov QWORD PTR [rbx+968], rax
	movabs rax, 993340341392051639
	mov QWORD PTR [rbx+976], rax
	movabs rax, 998406951103827405
	mov QWORD PTR [rbx+984], rax
	movabs rax, 1007977229162319333
	mov QWORD PTR [rbx+992], rax
	movabs rax, 1016984583038111231
	mov QWORD PTR [rbx+1000], rax
	movabs rax, 1023740085560348193
	mov QWORD PTR [rbx+1008], rax
	movabs rax, 860191994875451
	mov QWORD PTR [rbx+1016], rax
	movabs rax, 1040628841864564313
	mov QWORD PTR [rbx+1024], rax
	movabs rax, 1049073211427065461
	mov QWORD PTR [rbx+1032], rax
	movabs rax, 1060332390886084245
	mov QWORD PTR [rbx+1040], rax
	movabs rax, 1068776777628978873
	mov QWORD PTR [rbx+1048], rax
	movabs rax, 1078910005642333915
	mov QWORD PTR [rbx+1056], rax
	movabs rax, 1087354383794638599
	mov QWORD PTR [rbx+1064], rax
	movabs rax, 1099739437390696229
	mov QWORD PTR [rbx+1072], rax
	movabs rax, 1104243165869444935
	mov QWORD PTR [rbx+1080], rax
	movabs rax, 1110998668390633305
	mov QWORD PTR [rbx+1088], rax
	movabs rax, 1126761516198334335
	mov QWORD PTR [rbx+1096], rax
	movabs rax, 1131828143090110375
	mov QWORD PTR [rbx+1104], rax
	movabs rax, 1141961379693006779
	mov QWORD PTR [rbx+1112], rax
	movabs rax, 1152094650655248361
	mov QWORD PTR [rbx+1120], rax
	movabs rax, 1162227904437751811
	mov QWORD PTR [rbx+1128], rax
	movabs rax, 1170109315456634917
	mov QWORD PTR [rbx+1136], rax
	movabs rax, 1185309170359930943
	mov QWORD PTR [rbx+1144], rax
	movabs rax, 1190938790155980921
	mov QWORD PTR [rbx+1152], rax
	movabs rax, 1198820192584667281
	mov QWORD PTR [rbx+1160], rax
	movabs rax, 1205575677926903973
	mov QWORD PTR [rbx+1168], rax
	movabs rax, 1220775558599217345
	mov QWORD PTR [rbx+1176], rax
	movabs rax, 1228094036846121203
	mov QWORD PTR [rbx+1184], rax
	movabs rax, 1241042057576255765
	mov QWORD PTR [rbx+1192], rax
	movabs rax, 1251738295671918917
	mov QWORD PTR [rbx+1200], rax
	movabs rax, 1261308539371589987
	mov QWORD PTR [rbx+1208], rax
	movabs rax, 1270315927607251331
	mov QWORD PTR [rbx+1216], rax
	movabs rax, 1279886145536594341
	mov QWORD PTR [rbx+1224], rax
	movabs rax, 1290019433679491525
	mov QWORD PTR [rbx+1232], rax
	movabs rax, 1300715637415678447
	mov QWORD PTR [rbx+1240], rax
	movabs rax, 1308597108565021213
	mov QWORD PTR [rbx+1248], rax
	movabs rax, 1315352593906602539
	mov QWORD PTR [rbx+1256], rax
	movabs rax, 1328863564589634119
	mov QWORD PTR [rbx+1264], rax
	movabs rax, 1337307942742463091
	mov QWORD PTR [rbx+1272], rax
	movabs rax, 1348004223789240983
	mov QWORD PTR [rbx+1280], rax
	movabs rax, 1354759683360887481
	mov QWORD PTR [rbx+1288], rax
	movabs rax, 1371085489710240465
	mov QWORD PTR [rbx+1296], rax
	movabs rax, 1381781719217672973
	mov QWORD PTR [rbx+1304], rax
	movabs rax, 1389663147417342775
	mov QWORD PTR [rbx+1312], rax
	movabs rax, 1398107499799188303
	mov QWORD PTR [rbx+1320], rax
	movabs rax, 1405425978044126057
	mov QWORD PTR [rbx+1328], rax
	movabs rax, 1410492622116164487
	mov QWORD PTR [rbx+1336], rax
	movabs rax, 1421751750034920349
	mov QWORD PTR [rbx+1344], rax
	movabs rax, 1431885029588669379
	mov QWORD PTR [rbx+1352], rax
	movabs rax, 1439203490653869035
	mov QWORD PTR [rbx+1360], rax
	movabs rax, 1454403336967754751
	mov QWORD PTR [rbx+1368], rax
	movabs rax, 1462847740889994291
	mov QWORD PTR [rbx+1376], rax
	movabs rax, 1472981020443350105
	mov QWORD PTR [rbx+1384], rax
	movabs rax, 1485929049762894965
	mov QWORD PTR [rbx+1392], rax
	movabs rax, 1494373427915592865
	mov QWORD PTR [rbx+1400], rax
	movabs rax, 1506195565918360779
	mov QWORD PTR [rbx+1408], rax
	movabs rax, 1519706562372506885
	mov QWORD PTR [rbx+1416], rax
	movabs rax, 1525336164987639071
	mov QWORD PTR [rbx+1424], rax
	movabs rax, 1532091667509482807
	mov QWORD PTR [rbx+1432], rax
	movabs rax, 1542224921292117321
	mov QWORD PTR [rbx+1440], rax
	movabs rax, 1550106332311131499
	mov QWORD PTR [rbx+1448], rax
	movabs rax, 1556861834832713103
	mov QWORD PTR [rbx+1456], rax
	movabs rax, 1568683964245939637
	mov QWORD PTR [rbx+1464], rax
	movabs rax, 1587261544638911949
	mov QWORD PTR [rbx+1472], rax
	movabs rax, 1591202314575615497
	mov QWORD PTR [rbx+1480], rax
	movabs rax, 1599646641187132953
	mov QWORD PTR [rbx+1488], rax
	movabs rax, 1607528077976213049
	mov QWORD PTR [rbx+1496], rax
	movabs rax, 1616535449032529493
	mov QWORD PTR [rbx+1504], rax
	movabs rax, 1630046428306019957
	mov QWORD PTR [rbx+1512], rax
	movabs rax, 1638490806458193577
	mov QWORD PTR [rbx+1520], rax
	movabs rax, 1646372234657208003
	mov QWORD PTR [rbx+1528], rax
	movabs rax, 1651438861548590811
	mov QWORD PTR [rbx+1536], rax
	movabs rax, 1659883196750698221
	mov QWORD PTR [rbx+1544], rax
	movabs rax, 1671705343343925007
	mov QWORD PTR [rbx+1552], rax
	movabs rax, 1690845899462088513
	mov QWORD PTR [rbx+1560], rax
	movabs rax, 1700979213375182715
	mov QWORD PTR [rbx+1568], rax
	movabs rax, 1709423591527094175
	mov QWORD PTR [rbx+1576], rax
	movabs rax, 1717304993956566975
	mov QWORD PTR [rbx+1584], rax
	movabs rax, 1726312365012096993
	mov QWORD PTR [rbx+1592], rax
	movabs rax, 1737571501521442815
	mov QWORD PTR [rbx+1600], rax
	movabs rax, 1748267722438285365
	mov QWORD PTR [rbx+1608], rax
	movabs rax, 1758400933270460489
	mov QWORD PTR [rbx+1616], rax
	movabs rax, 1765156504512960625
	mov QWORD PTR [rbx+1624], rax
	movabs rax, 1773600882664872069
	mov QWORD PTR [rbx+1632], rax
	movabs rax, 1781482285093951655
	mov QWORD PTR [rbx+1640], rax
	movabs rax, 1789926663245994177
	mov QWORD PTR [rbx+1648], rax
	movabs rax, 1795556248681126105
	mov QWORD PTR [rbx+1656], rax
	movabs rax, 1809067253723633909
	mov QWORD PTR [rbx+1664], rax
	movabs rax, 1822015308814293297
	mov QWORD PTR [rbx+1672], rax
	movabs rax, 1837778130851010897
	mov QWORD PTR [rbx+1680], rax
	movabs rax, 1847348417502058899
	mov QWORD PTR [rbx+1688], rax
	movabs rax, 1852415070163376553
	mov QWORD PTR [rbx+1696], rax
	movabs rax, 1868177849250159047
	mov QWORD PTR [rbx+1704], rax
	movabs rax, 1878311128803777021
	mov QWORD PTR [rbx+1712], rax
	movabs rax, 1886192557002660375
	mov QWORD PTR [rbx+1720], rax
	movabs rax, 1895199876517796399
	mov QWORD PTR [rbx+1728], rax
	movabs rax, 1908147914428455505
	mov QWORD PTR [rbx+1736], rax
	movabs rax, 1914903442720496253
	mov QWORD PTR [rbx+1744], rax
	movabs rax, 1923347846642997927
	mov QWORD PTR [rbx+1752], rax
	movabs rax, 1933481091835435705
	mov QWORD PTR [rbx+1760], rax
	movabs rax, 1944177295570967255
	mov QWORD PTR [rbx+1768], rax
	movabs rax, 1955999450753473279
	mov QWORD PTR [rbx+1776], rax
	movabs rax, 1962191986143337263
	mov QWORD PTR [rbx+1784], rax
	movabs rax, 1969510438618471233
	mov QWORD PTR [rbx+1792], rax
	movabs rax, 1977954808180841305
	mov QWORD PTR [rbx+1800], rax
	movabs rax, 1989776920413412223
	mov QWORD PTR [rbx+1808], rax
	movabs rax, 2004413842544597927
	mov QWORD PTR [rbx+1816], rax
	movabs rax, 2015110072049933271
	mov QWORD PTR [rbx+1824], rax
	movabs rax, 2028621051324472329
	mov QWORD PTR [rbx+1832], rax
	movabs rax, 2034813612482960427
	mov QWORD PTR [rbx+1840], rax
	movabs rax, 2041569132185066565
	mov QWORD PTR [rbx+1848], rax
	movabs rax, 2057331988582440051
	mov QWORD PTR [rbx+1856], rax
	movabs rax, 2068591099322244249
	mov QWORD PTR [rbx+1864], rax
	movabs rax, 2086042805578833079
	mov QWORD PTR [rbx+1872], rax
	movabs rax, 2098990903619820793
	mov QWORD PTR [rbx+1880], rax
	movabs rax, 2107435281773042979
	mov QWORD PTR [rbx+1888], rax
	movabs rax, 2115879642744954177
	mov QWORD PTR [rbx+1896], rax
	movabs rax, 2122635171036994915
	mov QWORD PTR [rbx+1904], rax
	movabs rax, 2128264765061799291
	mov QWORD PTR [rbx+1912], rax
	movabs rax, 2136146167490747797
	mov QWORD PTR [rbx+1920], rax
	movabs rax, 2145153469826407847
	mov QWORD PTR [rbx+1928], rax
	movabs rax, 2158664449099767255
	mov QWORD PTR [rbx+1936], rax
	movabs rax, 2164857061798649337
	mov QWORD PTR [rbx+1944], rax
	movabs rax, 2173864389903851027
	mov QWORD PTR [rbx+1952], rax
	movabs rax, 2183434693733326383
	mov QWORD PTR [rbx+1960], rax
	movabs rax, 2200323364137803343
	mov QWORD PTR [rbx+1968], rax
	movabs rax, 2210456669460438671
	mov QWORD PTR [rbx+1976], rax
	movabs rax, 2217775173476622011
	mov QWORD PTR [rbx+1984], rax
	movabs rax, 2229034301395902155
	mov QWORD PTR [rbx+1992], rax
	movabs rax, 2237478679548337911
	mov QWORD PTR [rbx+2000], rax
	movabs rax, 2254367418671111951
	mov QWORD PTR [rbx+2008], rax
	movabs rax, 2266752515218415435
	mov QWORD PTR [rbx+2016], rax
	movabs rax, 2276322844818612091
	mov QWORD PTR [rbx+2024], rax
	movabs rax, 2283078330160586649
	mov QWORD PTR [rbx+2032], rax
	movabs rax, 2297152276566581173
	mov QWORD PTR [rbx+2040], rax
	mov eax, 128
	mov rcx, QWORD PTR [rdi+48]
	cmp rcx, 17
	jb 24f
	mov eax, 256
	jmp 25f
24:
25:
	mov QWORD PTR [rdi+208], rax
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
	mov r13d, 0
26:
	mov rax, QWORD PTR [rdi+48]
	add rax, 2
	add rax, rax
	add rax, rax
	add rax, rax
	mov rbx, QWORD PTR [rdi+120]
	add rbx, rax
	add rbx, rax
	add rbx, rax
	add rbx, rax
	mov rax, QWORD PTR [rbx+r13*8]
	mov QWORD PTR [rdi+216], rax
	mov rbx, QWORD PTR [rdi+216]
	and rbx, 65535
	mov rcx, rbx
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov r15d, 0
	sub r15, rcx
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
27:
	mov rsi, QWORD PTR [r8+r14*8]
	mov eax, esi
	add rax, rbp
	mov rcx, rax
	mul r15
	mov eax, eax
	mul rbx
	add rax, rcx
	shr rax, 32
	mov rbp, rax
	mov rax, rsi
	shr rax, 32
	add rax, rbp
	mov rcx, rax
	mul r15
	mov eax, eax
	mul rbx
	add rax, rcx
	shr rax, 32
	mov rbp, rax
	add r14, 1
	cmp r14, r12
	jne 27b
	mov rax, rbp
	cmp rax, 1
	sbb rdx, rdx
	xor rax, rbx
	cmp rax, 1
	sbb rcx, rcx
	or rdx, rcx
	or rdx, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+224], rdx
	mov rbx, QWORD PTR [rdi+216]
	shr rbx, 16
	and rbx, 65535
	mov rcx, rbx
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov r15d, 0
	sub r15, rcx
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
28:
	mov rsi, QWORD PTR [r8+r14*8]
	mov eax, esi
	add rax, rbp
	mov rcx, rax
	mul r15
	mov eax, eax
	mul rbx
	add rax, rcx
	shr rax, 32
	mov rbp, rax
	mov rax, rsi
	shr rax, 32
	add rax, rbp
	mov rcx, rax
	mul r15
	mov eax, eax
	mul rbx
	add rax, rcx
	shr rax, 32
	mov rbp, rax
	add r14, 1
	cmp r14, r12
	jne 28b
	mov rax, rbp
	cmp rax, 1
	sbb rdx, rdx
	xor rax, rbx
	cmp rax, 1
	sbb rcx, rcx
	or rdx, rcx
	or rdx, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+224], rdx
	mov rbx, QWORD PTR [rdi+216]
	shr rbx, 32
	and rbx, 65535
	mov rcx, rbx
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov r15d, 0
	sub r15, rcx
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
29:
	mov rsi, QWORD PTR [r8+r14*8]
	mov eax, esi
	add rax, rbp
	mov rcx, rax
	mul r15
	mov eax, eax
	mul rbx
	add rax, rcx
	shr rax, 32
	mov rbp, rax
	mov rax, rsi
	shr rax, 32
	add rax, rbp
	mov rcx, rax
	mul r15
	mov eax, eax
	mul rbx
	add rax, rcx
	shr rax, 32
	mov rbp, rax
	add r14, 1
	cmp r14, r12
	jne 29b
	mov rax, rbp
	cmp rax, 1
	sbb rdx, rdx
	xor rax, rbx
	cmp rax, 1
	sbb rcx, rcx
	or rdx, rcx
	or rdx, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+224], rdx
	mov rbx, QWORD PTR [rdi+216]
	shr rbx, 48
	and rbx, 65535
	mov rcx, rbx
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov rax, rbx
	mul rcx
	mov esi, 2
	sub rsi, rax
	mov rax, rcx
	mul rsi
	mov rcx, rax
	mov r15d, 0
	sub r15, rcx
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
210:
	mov rsi, QWORD PTR [r8+r14*8]
	mov eax, esi
	add rax, rbp
	mov rcx, rax
	mul r15
	mov eax, eax
	mul rbx
	add rax, rcx
	shr rax, 32
	mov rbp, rax
	mov rax, rsi
	shr rax, 32
	add rax, rbp
	mov rcx, rax
	mul r15
	mov eax, eax
	mul rbx
	add rax, rcx
	shr rax, 32
	mov rbp, rax
	add r14, 1
	cmp r14, r12
	jne 210b
	mov rax, rbp
	cmp rax, 1
	sbb rdx, rdx
	xor rax, rbx
	cmp rax, 1
	sbb rcx, rcx
	or rdx, rcx
	or rdx, QWORD PTR [rdi+224]
	mov QWORD PTR [rdi+224], rdx
	add r13, 1
	mov rax, QWORD PTR [rdi+208]
	cmp r13, rax
	jne 26b
	mov rax, QWORD PTR [rdi+224]
	test rax, rax
	je 211f
	mov eax, 3
	mov QWORD PTR [rdi+232], rax
	jmp 212f
211:
	call {vg_dsa_prime_setup_adx}
	mov eax, 1
	mov QWORD PTR [rdi+160], rax
	mov eax, 0
	mov QWORD PTR [rdi+168], rax
213:
	mov rcx, QWORD PTR [rdi+192]
	mov rax, QWORD PTR [rdi+200]
	sub rcx, rax
	mov rax, QWORD PTR [rdi+136]
	cmp rcx, rax
	jb 214f
	mov r15, rdi
	mov rsi, QWORD PTR [rdi+184]
	mov rax, QWORD PTR [rdi+200]
	add rax, QWORD PTR [rdi+136]
	mov QWORD PTR [rdi+200], rax
	add rsi, rax
	mov rcx, QWORD PTR [rdi+144]
	sub rsi, rcx
	mov rdi, QWORD PTR [rdi+128]
	mov rdx, rcx
	shl rdx, 3
	sub rdx, 1
	and rdx, 7
	mov r8d, 127
	mov r9d, 128
	cmp rdx, 0
	mov r10d, 0
	cmove r8, r10
	mov r10d, 1
	cmove r9, r10
	cmp rdx, 1
	mov r10d, 1
	cmove r8, r10
	mov r10d, 2
	cmove r9, r10
	cmp rdx, 2
	mov r10d, 3
	cmove r8, r10
	mov r10d, 4
	cmove r9, r10
	cmp rdx, 3
	mov r10d, 7
	cmove r8, r10
	mov r10d, 8
	cmove r9, r10
	cmp rdx, 4
	mov r10d, 15
	cmove r8, r10
	mov r10d, 16
	cmove r9, r10
	cmp rdx, 5
	mov r10d, 31
	cmove r8, r10
	mov r10d, 32
	cmove r9, r10
	cmp rdx, 6
	mov r10d, 63
	cmove r8, r10
	mov r10d, 64
	cmove r9, r10
	or r8, r9
	mov r9d, 0
	mov r10, rsi
	mov r11, rdi
	movzx eax, BYTE PTR [r10]
	and rax, r8
	or rax, r9
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
216:
	movzx eax, BYTE PTR [r10]
	mov BYTE PTR [r11], al
	add r10, 1
	add r11, 1
	sub rcx, 1
	jne 216b
	mov rdi, r15
	mov r8, QWORD PTR [rdi+104]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
217:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 217b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rsi, QWORD PTR [rdi+128]
	mov rcx, QWORD PTR [rdi+144]
	mov rbx, QWORD PTR [rdi+104]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
218:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 219f
	jmp 220f
219:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
220:
	test rdx, rdx
	jne 218b
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+120]
	mov r10, QWORD PTR [rdi+104]
	mov ebp, 0
	mov r14, 0
221:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 221b
	mov rax, rbp
	and rax, 1
	mov QWORD PTR [rdi+240], rax
	mov r12, QWORD PTR [rdi+48]
	mov rsi, QWORD PTR [rdi+104]
	mov rbx, QWORD PTR [rdi+88]
	mov r14, 0
222:
	mov rax, QWORD PTR [rsi+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 222b
	mov rbx, QWORD PTR [rdi+88]
	mov rax, QWORD PTR [rbx]
	or rax, 1
	mov QWORD PTR [rbx], rax
	mov r12, QWORD PTR [rdi+48]
	mov rbx, QWORD PTR [rdi+88]
	mov r10, QWORD PTR [rdi+64]
	mov ebp, 0
	mov r14, 0
223:
	add rbp, rbp
	mov rax, QWORD PTR [rbx+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 223b
	mov rax, rbp
	and rax, 1
	and rax, QWORD PTR [rdi+240]
	mov QWORD PTR [rdi+240], rax
	test rax, rax
	mov ecx, 0
	sub rcx, rax
	mov QWORD PTR [rdi+240], rcx
	test rax, rax
	je 224f
	jmp 225f
224:
	mov rbx, rdi
	mov rcx, QWORD PTR [rdi+144]
	mov rdi, QWORD PTR [rdi+128]
	movzx eax, BYTE PTR [rdi]
	and rax, 127
	mov BYTE PTR [rdi], al
	movzx eax, BYTE PTR [rdi+rcx*1-1]
	or rax, 2
	mov BYTE PTR [rdi+rcx*1-1], al
	mov rdi, rbx
	mov r8, QWORD PTR [rdi+104]
	mov r12, QWORD PTR [rdi+48]
	mov eax, 0
	mov r14, 0
226:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 226b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov rsi, QWORD PTR [rdi+128]
	mov rcx, QWORD PTR [rdi+144]
	mov rbx, QWORD PTR [rdi+104]
	mov eax, 0
	mov rdx, rcx
	mov r14, rsi
227:
	sub rdx, 1
	ror rax, 56
	movzx ebp, BYTE PTR [r14]
	add rax, rbp
	add r14, 1
	mov rbp, rdx
	and rbp, 7
	je 228f
	jmp 229f
228:
	mov rbp, rdx
	shr rbp, 3
	mov QWORD PTR [rbx+rbp*8], rax
	mov eax, 0
229:
	test rdx, rdx
	jne 227b
225:
	mov edx, 5
	mov ecx, 5
	mov r8d, 4
	mov edx, edx
	mov ecx, ecx
	mov r8d, r8d
	movq xmm8, rbx
	movq xmm9, rbp
	movq xmm10, r12
	movq xmm11, r13
	movq xmm12, r14
	movq xmm13, r15
	movdqu xmm3, XMMWORD PTR [rdi+128]
	movdqu xmm4, XMMWORD PTR [rdi+144]
	movdqu xmm5, XMMWORD PTR [rdi+160]
	movdqu xmm6, XMMWORD PTR [rdi+224]
	movdqu xmm7, XMMWORD PTR [rdi+240]
	mov rax, QWORD PTR [rdi+rdx*8+64]
	mov QWORD PTR [rdi+128], rax
	mov rax, QWORD PTR [rdi+rcx*8+64]
	mov QWORD PTR [rdi+136], rax
	mov rax, QWORD PTR [rdi+r8*8+64]
	mov QWORD PTR [rdi+144], rax
	mov rax, QWORD PTR [rdi+48]
	sub rax, 8
	ror rax, 3
	shr rax, 27
	je 230f
	mov rbx, QWORD PTR [rdi+rdx*8+64]
	mov r11, QWORD PTR [rdi+rcx*8+64]
	mov r9, QWORD PTR [rdi+r8*8+64]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	mov r12, QWORD PTR [rdi+48]
	mov r15, QWORD PTR [rdi+56]
	mov rsi, QWORD PTR [rdi+88]
	mov eax, 0
	mov r14, 0
232:
	mov QWORD PTR [r8+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 232b
	mov QWORD PTR [r8+r12*8], rax
	mov QWORD PTR [r8+r12*8+8], rax
	mov r13, 0
233:
	mov rcx, QWORD PTR [r11+r13*8]
	mov ebp, 0
	mov r14, 0
234:
	mov rax, QWORD PTR [r9+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 234b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	mov rax, QWORD PTR [r8]
	mul r15
	mov rcx, rax
	mov rax, QWORD PTR [r10]
	mul rcx
	add rax, QWORD PTR [r8]
	adc rdx, 0
	mov rbp, rdx
	mov r14, 1
235:
	mov rax, QWORD PTR [r10+r14*8]
	mul rcx
	add rax, QWORD PTR [r8+r14*8]
	adc rdx, 0
	add rax, rbp
	adc rdx, 0
	mov QWORD PTR [r8+r14*8-8], rax
	mov rbp, rdx
	add r14, 1
	cmp r14, r12
	jne 235b
	mov rax, QWORD PTR [r8+r12*8]
	add rax, rbp
	mov QWORD PTR [r8+r12*8-8], rax
	mov rax, QWORD PTR [r8+r12*8+8]
	adc rax, 0
	mov QWORD PTR [r8+r12*8], rax
	mov eax, 0
	mov QWORD PTR [r8+r12*8+8], rax
	add r13, 1
	cmp r13, r12
	jne 233b
	mov ebp, 0
	mov r14, 0
236:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	sbb rbp, rbp
	add r14, 1
	cmp r14, r12
	jne 236b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
237:
	mov rax, QWORD PTR [r8+r14*8]
	mov rdx, QWORD PTR [rsi+r14*8]
	xor rax, rdx
	and rax, rbp
	xor rax, rdx
	mov QWORD PTR [rbx+r14*8], rax
	add r14, 1
	cmp r14, r12
	jne 237b
	jmp 231f
230:
	cmp rcx, r8
	je 238f
	mov r9, QWORD PTR [rdi+144]
	mov r10, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rdi+80]
	add r8, 16
	mov rbx, QWORD PTR [rdi+48]
	mov eax, 0
	mov rcx, rbx
	add rcx, rcx
	mov r14d, 0
240:
	mov QWORD PTR [r8+r14*8], rax
	mov QWORD PTR [r8+r14*8+8], rax
	mov QWORD PTR [r8+r14*8+16], rax
	mov QWORD PTR [r8+r14*8+24], rax
	mov QWORD PTR [r8+r14*8+32], rax
	mov QWORD PTR [r8+r14*8+40], rax
	mov QWORD PTR [r8+r14*8+48], rax
	mov QWORD PTR [r8+r14*8+56], rax
	add r14, 8
	cmp r14, rcx
	jne 240b
	mov QWORD PTR [r8+r14*8], rax
	mov QWORD PTR [r8+r14*8+8], rax
	mov eax, 0
	mov QWORD PTR [rdi+224], rax
241:
	mov eax, 0
	mov QWORD PTR [rdi+240], rax
	mov QWORD PTR [rdi+232], rax
	mov rax, QWORD PTR [rdi+224]
	shl rax, 3
	mov rcx, QWORD PTR [rdi+136]
	add rcx, rax
	mov rdx, QWORD PTR [rdi+232]
	shl rdx, 3
	mov rbp, QWORD PTR [rdi+144]
	add rbp, rdx
	add rax, rdx
	mov rsi, QWORD PTR [rdi+80]
	add rsi, rax
	add rsi, 16
	mov r8, QWORD PTR [rsi]
	mov r9, QWORD PTR [rsi+8]
	mov r10, QWORD PTR [rsi+16]
	mov r11, QWORD PTR [rsi+24]
	mov r12, QWORD PTR [rsi+32]
	mov r13, QWORD PTR [rsi+40]
	mov r14, QWORD PTR [rsi+48]
	mov r15, QWORD PTR [rsi+56]
242:
	mov rdx, QWORD PTR [rcx]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi], rbx
	mov rdx, QWORD PTR [rcx+8]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+8], rbx
	mov rdx, QWORD PTR [rcx+16]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+16], rbx
	mov rdx, QWORD PTR [rcx+24]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+24], rbx
	mov rdx, QWORD PTR [rcx+32]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+32], rbx
	mov rdx, QWORD PTR [rcx+40]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+40], rbx
	mov rdx, QWORD PTR [rcx+48]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+48], rbx
	mov rdx, QWORD PTR [rcx+56]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+56], rbx
	mov rdx, QWORD PTR [rdi+240]
	add rsi, 64
	xor eax, eax
	adcx r8, QWORD PTR [rsi]
	adox r8, rdx
	adcx r9, QWORD PTR [rsi+8]
	adox r9, rax
	adcx r10, QWORD PTR [rsi+16]
	adox r10, rax
	adcx r11, QWORD PTR [rsi+24]
	adox r11, rax
	adcx r12, QWORD PTR [rsi+32]
	adox r12, rax
	adcx r13, QWORD PTR [rsi+40]
	adox r13, rax
	adcx r14, QWORD PTR [rsi+48]
	adox r14, rax
	adcx r15, QWORD PTR [rsi+56]
	adox r15, rax
	mov edx, 0
	adcx rax, rdx
	adox rax, rdx
	mov QWORD PTR [rdi+240], rax
	add rbp, 64
	mov rax, QWORD PTR [rdi+232]
	add rax, 8
	mov QWORD PTR [rdi+232], rax
	cmp rax, QWORD PTR [rdi+48]
	jne 242b
	mov QWORD PTR [rsi], r8
	mov QWORD PTR [rsi+8], r9
	mov QWORD PTR [rsi+16], r10
	mov QWORD PTR [rsi+24], r11
	mov QWORD PTR [rsi+32], r12
	mov QWORD PTR [rsi+40], r13
	mov QWORD PTR [rsi+48], r14
	mov QWORD PTR [rsi+56], r15
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	cmp rax, QWORD PTR [rdi+48]
	je 243f
	mov rbp, QWORD PTR [rdi+240]
	add rsi, 64
	mov rdx, QWORD PTR [rdi+48]
	shl rdx, 4
	add rdx, QWORD PTR [rdi+80]
	add rdx, 16
	mov ecx, 0
245:
	mov r8, QWORD PTR [rsi]
	mov r9, QWORD PTR [rsi+8]
	mov r10, QWORD PTR [rsi+16]
	mov r11, QWORD PTR [rsi+24]
	mov r12, QWORD PTR [rsi+32]
	mov r13, QWORD PTR [rsi+40]
	mov r14, QWORD PTR [rsi+48]
	mov r15, QWORD PTR [rsi+56]
	xor eax, eax
	adcx r8, rbp
	adcx r9, rcx
	adcx r10, rcx
	adcx r11, rcx
	adcx r12, rcx
	adcx r13, rcx
	adcx r14, rcx
	adcx r15, rcx
	mov ebp, 0
	adcx rbp, rax
	mov QWORD PTR [rsi], r8
	mov QWORD PTR [rsi+8], r9
	mov QWORD PTR [rsi+16], r10
	mov QWORD PTR [rsi+24], r11
	mov QWORD PTR [rsi+32], r12
	mov QWORD PTR [rsi+40], r13
	mov QWORD PTR [rsi+48], r14
	mov QWORD PTR [rsi+56], r15
	add rsi, 64
	cmp rsi, rdx
	jne 245b
	jmp 244f
243:
244:
	mov rax, QWORD PTR [rdi+224]
	add rax, 8
	mov QWORD PTR [rdi+224], rax
	cmp rax, QWORD PTR [rdi+48]
	jne 241b
	mov r8, QWORD PTR [rdi+80]
	mov r9, QWORD PTR [rdi+48]
	shl r9, 4
	add r9, r8
	add r9, 16
	mov eax, 0
	mov QWORD PTR [r9], rax
	mov QWORD PTR [r9+8], rax
	jmp 239f
238:
239:
	mov rcx, QWORD PTR [rdi+80]
	add rcx, 16
	mov eax, 0
	mov QWORD PTR [rcx-16], rax
246:
	mov rsi, rcx
	mov rbp, QWORD PTR [rdi+64]
	mov r8, QWORD PTR [rsi]
	mov r9, QWORD PTR [rsi+8]
	mov r10, QWORD PTR [rsi+16]
	mov r11, QWORD PTR [rsi+24]
	mov r12, QWORD PTR [rsi+32]
	mov r13, QWORD PTR [rsi+40]
	mov r14, QWORD PTR [rsi+48]
	mov r15, QWORD PTR [rsi+56]
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx+8], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx+16], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx+24], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx+32], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx+40], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx+48], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov rdx, r8
	mulx rax, rdx, QWORD PTR [rdi+56]
	mov QWORD PTR [rcx+56], rdx
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov eax, 0
	mov QWORD PTR [rcx-8], rax
	add rbp, 64
	add rsi, 64
	mov rax, QWORD PTR [rdi+48]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, QWORD PTR [rdi+64]
	cmp rbp, rax
	jne 247f
	jmp 248f
247:
249:
	mov rdx, QWORD PTR [rcx-8]
	add rdx, -1
	adcx r8, QWORD PTR [rsi]
	adcx r9, QWORD PTR [rsi+8]
	adcx r10, QWORD PTR [rsi+16]
	adcx r11, QWORD PTR [rsi+24]
	adcx r12, QWORD PTR [rsi+32]
	adcx r13, QWORD PTR [rsi+40]
	adcx r14, QWORD PTR [rsi+48]
	adcx r15, QWORD PTR [rsi+56]
	mov eax, 0
	adcx rax, rax
	mov QWORD PTR [rcx-8], rax
	mov rdx, QWORD PTR [rcx]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi], rbx
	mov rdx, QWORD PTR [rcx+8]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+8], rbx
	mov rdx, QWORD PTR [rcx+16]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+16], rbx
	mov rdx, QWORD PTR [rcx+24]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+24], rbx
	mov rdx, QWORD PTR [rcx+32]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+32], rbx
	mov rdx, QWORD PTR [rcx+40]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+40], rbx
	mov rdx, QWORD PTR [rcx+48]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+48], rbx
	mov rdx, QWORD PTR [rcx+56]
	mov rbx, r8
	xor eax, eax
	mulx r8, rax, QWORD PTR [rbp]
	adcx rbx, rax
	adox r8, r9
	mulx r9, rax, QWORD PTR [rbp+8]
	adcx r8, rax
	adox r9, r10
	mulx r10, rax, QWORD PTR [rbp+16]
	adcx r9, rax
	adox r10, r11
	mulx r11, rax, QWORD PTR [rbp+24]
	adcx r10, rax
	adox r11, r12
	mulx r12, rax, QWORD PTR [rbp+32]
	adcx r11, rax
	adox r12, r13
	mulx r13, rax, QWORD PTR [rbp+40]
	adcx r12, rax
	adox r13, r14
	mulx r14, rax, QWORD PTR [rbp+48]
	adcx r13, rax
	adox r14, r15
	mulx r15, rax, QWORD PTR [rbp+56]
	adcx r14, rax
	mov eax, 0
	adox r15, rax
	adcx r15, rax
	mov QWORD PTR [rsi+56], rbx
	add rbp, 64
	add rsi, 64
	mov rax, QWORD PTR [rdi+48]
	add rax, rax
	add rax, rax
	add rax, rax
	add rax, QWORD PTR [rdi+64]
	cmp rbp, rax
	jne 249b
248:
	mov rdx, QWORD PTR [rcx-8]
	add rdx, -1
	mov eax, 0
	mov rdx, QWORD PTR [rcx-16]
	adcx r8, QWORD PTR [rsi]
	adox r8, rdx
	adcx r9, QWORD PTR [rsi+8]
	adox r9, rax
	adcx r10, QWORD PTR [rsi+16]
	adox r10, rax
	adcx r11, QWORD PTR [rsi+24]
	adox r11, rax
	adcx r12, QWORD PTR [rsi+32]
	adox r12, rax
	adcx r13, QWORD PTR [rsi+40]
	adox r13, rax
	adcx r14, QWORD PTR [rsi+48]
	adox r14, rax
	adcx r15, QWORD PTR [rsi+56]
	adox r15, rax
	mov edx, 0
	adcx rax, rdx
	adox rax, rdx
	mov QWORD PTR [rsi], r8
	mov QWORD PTR [rsi+8], r9
	mov QWORD PTR [rsi+16], r10
	mov QWORD PTR [rsi+24], r11
	mov QWORD PTR [rsi+32], r12
	mov QWORD PTR [rsi+40], r13
	mov QWORD PTR [rsi+48], r14
	mov QWORD PTR [rsi+56], r15
	mov QWORD PTR [rcx+48], rax
	add rcx, 64
	cmp rcx, QWORD PTR [rdi+88]
	jne 246b
	mov r8, rcx
	mov rbp, QWORD PTR [rdi+48]
	mov r10, QWORD PTR [rcx-16]
	mov QWORD PTR [r8+rbp*8], r10
	mov eax, 0
	mov QWORD PTR [r8+rbp*8+8], rax
	mov r10, QWORD PTR [rdi+64]
	mov r12, QWORD PTR [rdi+48]
	mov r8, QWORD PTR [rdi+88]
	mov rsi, QWORD PTR [rdi+80]
	mov rbx, QWORD PTR [rdi+128]
	mov ebp, 0
	mov r14, 0
250:
	add rbp, rbp
	mov rax, QWORD PTR [r8+r14*8]
	sbb rax, QWORD PTR [r10+r14*8]
	mov QWORD PTR [rsi+r14*8], rax
	mov rax, QWORD PTR [r8+r14*8+8]
	sbb rax, QWORD PTR [r10+r14*8+8]
	mov QWORD PTR [rsi+r14*8+8], rax
	mov rax, QWORD PTR [r8+r14*8+16]
	sbb rax, QWORD PTR [r10+r14*8+16]
	mov QWORD PTR [rsi+r14*8+16], rax
	mov rax, QWORD PTR [r8+r14*8+24]
	sbb rax, QWORD PTR [r10+r14*8+24]
	mov QWORD PTR [rsi+r14*8+24], rax
	mov rax, QWORD PTR [r8+r14*8+32]
	sbb rax, QWORD PTR [r10+r14*8+32]
	mov QWORD PTR [rsi+r14*8+32], rax
	mov rax, QWORD PTR [r8+r14*8+40]
	sbb rax, QWORD PTR [r10+r14*8+40]
	mov QWORD PTR [rsi+r14*8+40], rax
	mov rax, QWORD PTR [r8+r14*8+48]
	sbb rax, QWORD PTR [r10+r14*8+48]
	mov QWORD PTR [rsi+r14*8+48], rax
	mov rax, QWORD PTR [r8+r14*8+56]
	sbb rax, QWORD PTR [r10+r14*8+56]
	mov QWORD PTR [rsi+r14*8+56], rax
	sbb rbp, rbp
	add r14, 8
	cmp r14, r12
	jne 250b
	mov rax, QWORD PTR [r8+r12*8]
	add rbp, rbp
	sbb rax, 0
	sbb rbp, rbp
	mov r14, 0
251:
	add rbp, rbp
	mov rax, QWORD PTR [rsi+r14*8]
	cmovb rax, QWORD PTR [r8+r14*8]
	mov QWORD PTR [rbx+r14*8], rax
	mov rax, QWORD PTR [rsi+r14*8+8]
	cmovb rax, QWORD PTR [r8+r14*8+8]
	mov QWORD PTR [rbx+r14*8+8], rax
	mov rax, QWORD PTR [rsi+r14*8+16]
	cmovb rax, QWORD PTR [r8+r14*8+16]
	mov QWORD PTR [rbx+r14*8+16], rax
	mov rax, QWORD PTR [rsi+r14*8+24]
	cmovb rax, QWORD PTR [r8+r14*8+24]
	mov QWORD PTR [rbx+r14*8+24], rax
	mov rax, QWORD PTR [rsi+r14*8+32]
	cmovb rax, QWORD PTR [r8+r14*8+32]
	mov QWORD PTR [rbx+r14*8+32], rax
	mov rax, QWORD PTR [rsi+r14*8+40]
	cmovb rax, QWORD PTR [r8+r14*8+40]
	mov QWORD PTR [rbx+r14*8+40], rax
	mov rax, QWORD PTR [rsi+r14*8+48]
	cmovb rax, QWORD PTR [r8+r14*8+48]
	mov QWORD PTR [rbx+r14*8+48], rax
	mov rax, QWORD PTR [rsi+r14*8+56]
	cmovb rax, QWORD PTR [r8+r14*8+56]
	mov QWORD PTR [rbx+r14*8+56], rax
	sbb rbp, rbp
	add r14, 8
	cmp r14, r12
	jne 251b
231:
	movq rbx, xmm8
	movq rbp, xmm9
	movq r12, xmm10
	movq r13, xmm11
	movq r14, xmm12
	movq r15, xmm13
	movdqu XMMWORD PTR [rdi+128], xmm3
	movdqu XMMWORD PTR [rdi+144], xmm4
	movdqu XMMWORD PTR [rdi+160], xmm5
	movdqu XMMWORD PTR [rdi+224], xmm6
	movdqu XMMWORD PTR [rdi+240], xmm7
	mov rax, QWORD PTR [rdi+48]
	mov rcx, 208
	imul rcx, rax
	add rcx, 656
	add rcx, rdi
	mov QWORD PTR [rcx], rbx
	mov rbx, rdi
	mov rsi, rax
	mov rdx, 28
	imul rsi, rdx
	add rsi, 88
	call {vg_miller_rabin_round_adx}
	mov rdi, rbx
	mov eax, eax
	mov rcx, 0
	sub rcx, rax
	mov QWORD PTR [rdi+176], rcx
	mov rax, QWORD PTR [rdi+48]
	mov rcx, 208
	imul rcx, rax
	add rcx, 656
	add rcx, rdi
	mov rbx, QWORD PTR [rcx]
	mov ecx, 3
	mov rax, QWORD PTR [rdi+176]
	test rax, rax
	je 252f
	mov rax, QWORD PTR [rdi+160]
	add rax, 1
	mov QWORD PTR [rdi+160], rax
	mov rdx, QWORD PTR [rdi+240]
	and rdx, 1
	add rdx, QWORD PTR [rdi+168]
	mov QWORD PTR [rdi+168], rdx
	cmp rax, 17
	sbb rcx, rcx
	cmp rdx, QWORD PTR [rdi+152]
	sbb rax, rax
	or rcx, rax
	and rcx, 3
	add rcx, 1
	jmp 253f
252:
253:
	mov QWORD PTR [rdi+232], rcx
	jmp 215f
214:
	mov eax, 0
	mov QWORD PTR [rdi+232], rax
215:
	mov rax, QWORD PTR [rdi+232]
	cmp rax, 4
	je 213b
212:
	mov rax, QWORD PTR [rdi+200]
	mov r8, QWORD PTR [rsp+48]
	mov QWORD PTR [r8], rax
	mov rax, QWORD PTR [rdi+232]
	mov rcx, rax
	shr rcx, 1
	sub rax, rcx
	mov rbx, QWORD PTR [rsp]
	mov rbp, QWORD PTR [rsp+8]
	mov r12, QWORD PTR [rsp+16]
	mov r13, QWORD PTR [rsp+24]
	mov r14, QWORD PTR [rsp+32]
	mov r15, QWORD PTR [rsp+40]
	lea rsp, [rsp+56]
	ret
	.p2align 6

theory gate_2
  imports gate_1
begin
(*begin*)
reserve a, b, c, d for "setHIDDENM2"
mtheorem gate_2_th_1:
" for s0 be setHIDDENM2 holds  for s1 be setHIDDENM2 holds  for s2 be setHIDDENM2 holds  for s3 be setHIDDENM2 holds  for s4 be setHIDDENM2 holds  for s5 be setHIDDENM2 holds  for s6 be setHIDDENM2 holds  for s7 be setHIDDENM2 holds  for ns0 be setHIDDENM2 holds  for ns1 be setHIDDENM2 holds  for ns2 be setHIDDENM2 holds  for ns3 be setHIDDENM2 holds  for ns4 be setHIDDENM2 holds  for ns5 be setHIDDENM2 holds  for ns6 be setHIDDENM2 holds  for ns7 be setHIDDENM2 holds  for q1 be setHIDDENM2 holds  for q2 be setHIDDENM2 holds  for q3 be setHIDDENM2 holds  for nq1 be setHIDDENM2 holds  for nq2 be setHIDDENM2 holds  for nq3 be setHIDDENM2 holds ((((((((((((((((((s0 be  non emptyXBOOLE-0V1 iff  not AND3GATE-1K8(NOT1GATE-1K1 q3,NOT1GATE-1K1 q2,NOT1GATE-1K1 q1) be emptyXBOOLE-0V1) & (s1 be  non emptyXBOOLE-0V1 iff  not AND3GATE-1K8(NOT1GATE-1K1 q3,NOT1GATE-1K1 q2,q1) be emptyXBOOLE-0V1)) & (s2 be  non emptyXBOOLE-0V1 iff  not AND3GATE-1K8(NOT1GATE-1K1 q3,q2,NOT1GATE-1K1 q1) be emptyXBOOLE-0V1)) & (s3 be  non emptyXBOOLE-0V1 iff  not AND3GATE-1K8(NOT1GATE-1K1 q3,q2,q1) be emptyXBOOLE-0V1)) & (s4 be  non emptyXBOOLE-0V1 iff  not AND3GATE-1K8(q3,NOT1GATE-1K1 q2,NOT1GATE-1K1 q1) be emptyXBOOLE-0V1)) & (s5 be  non emptyXBOOLE-0V1 iff  not AND3GATE-1K8(q3,NOT1GATE-1K1 q2,q1) be emptyXBOOLE-0V1)) & (s6 be  non emptyXBOOLE-0V1 iff  not AND3GATE-1K8(q3,q2,NOT1GATE-1K1 q1) be emptyXBOOLE-0V1)) & (s7 be  non emptyXBOOLE-0V1 iff  not AND3GATE-1K8(q3,q2,q1) be emptyXBOOLE-0V1)) & (ns0 be  non emptyXBOOLE-0V1 iff  not AND3GATE-1K8(NOT1GATE-1K1 nq3,NOT1GATE-1K1 nq2,NOT1GATE-1K1 nq1) be emptyXBOOLE-0V1)) & (ns1 be  non emptyXBOOLE-0V1 iff  not AND3GATE-1K8(NOT1GATE-1K1 nq3,NOT1GATE-1K1 nq2,nq1) be emptyXBOOLE-0V1)) & (ns2 be  non emptyXBOOLE-0V1 iff  not AND3GATE-1K8(NOT1GATE-1K1 nq3,nq2,NOT1GATE-1K1 nq1) be emptyXBOOLE-0V1)) & (ns3 be  non emptyXBOOLE-0V1 iff  not AND3GATE-1K8(NOT1GATE-1K1 nq3,nq2,nq1) be emptyXBOOLE-0V1)) & (ns4 be  non emptyXBOOLE-0V1 iff  not AND3GATE-1K8(nq3,NOT1GATE-1K1 nq2,NOT1GATE-1K1 nq1) be emptyXBOOLE-0V1)) & (ns5 be  non emptyXBOOLE-0V1 iff  not AND3GATE-1K8(nq3,NOT1GATE-1K1 nq2,nq1) be emptyXBOOLE-0V1)) & (ns6 be  non emptyXBOOLE-0V1 iff  not AND3GATE-1K8(nq3,nq2,NOT1GATE-1K1 nq1) be emptyXBOOLE-0V1)) & (ns7 be  non emptyXBOOLE-0V1 iff  not AND3GATE-1K8(nq3,nq2,nq1) be emptyXBOOLE-0V1)) & (nq1 be  non emptyXBOOLE-0V1 iff  not NOT1GATE-1K1 q1 be emptyXBOOLE-0V1)) & (nq2 be  non emptyXBOOLE-0V1 iff  not XOR2GATE-1K4(q1,q2) be emptyXBOOLE-0V1)) & (nq3 be  non emptyXBOOLE-0V1 iff  not OR2GATE-1K3(AND2GATE-1K2(q3,NOT1GATE-1K1 q1),AND2GATE-1K2(q1,XOR2GATE-1K4(q2,q3))) be emptyXBOOLE-0V1) implies (((((((ns1 be  non emptyXBOOLE-0V1 iff s0 be  non emptyXBOOLE-0V1) & (ns2 be  non emptyXBOOLE-0V1 iff s1 be  non emptyXBOOLE-0V1)) & (ns3 be  non emptyXBOOLE-0V1 iff s2 be  non emptyXBOOLE-0V1)) & (ns4 be  non emptyXBOOLE-0V1 iff s3 be  non emptyXBOOLE-0V1)) & (ns5 be  non emptyXBOOLE-0V1 iff s4 be  non emptyXBOOLE-0V1)) & (ns6 be  non emptyXBOOLE-0V1 iff s5 be  non emptyXBOOLE-0V1)) & (ns7 be  non emptyXBOOLE-0V1 iff s6 be  non emptyXBOOLE-0V1)) & (ns0 be  non emptyXBOOLE-0V1 iff s7 be  non emptyXBOOLE-0V1)"
sorry

mtheorem gate_2_th_2:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds  for d be setHIDDENM2 holds AND3GATE-1K8(AND2GATE-1K2(a,d),AND2GATE-1K2(b,d),AND2GATE-1K2(c,d)) be  non emptyXBOOLE-0V1 iff AND2GATE-1K2(AND3GATE-1K8(a,b,c),d) be  non emptyXBOOLE-0V1"
sorry

mtheorem gate_2_th_3:
" for a be setHIDDENM2 holds  for b be setHIDDENM2 holds  for c be setHIDDENM2 holds  for d be setHIDDENM2 holds ((( not AND2GATE-1K2(a,b) be  non emptyXBOOLE-0V1 iff OR2GATE-1K3(NOT1GATE-1K1 a,NOT1GATE-1K1 b) be  non emptyXBOOLE-0V1) & (OR2GATE-1K3(a,b) be  non emptyXBOOLE-0V1 & OR2GATE-1K3(c,b) be  non emptyXBOOLE-0V1 iff OR2GATE-1K3(AND2GATE-1K2(a,c),b) be  non emptyXBOOLE-0V1)) & ((OR2GATE-1K3(a,b) be  non emptyXBOOLE-0V1 & OR2GATE-1K3(c,b) be  non emptyXBOOLE-0V1) & OR2GATE-1K3(d,b) be  non emptyXBOOLE-0V1 iff OR2GATE-1K3(AND3GATE-1K8(a,c,d),b) be  non emptyXBOOLE-0V1)) & (OR2GATE-1K3(a,b) be  non emptyXBOOLE-0V1 & (a be  non emptyXBOOLE-0V1 iff c be  non emptyXBOOLE-0V1) implies OR2GATE-1K3(c,b) be  non emptyXBOOLE-0V1)"
sorry

mtheorem gate_2_th_4:
" for s0 be setHIDDENM2 holds  for s1 be setHIDDENM2 holds  for s2 be setHIDDENM2 holds  for s3 be setHIDDENM2 holds  for s4 be setHIDDENM2 holds  for s5 be setHIDDENM2 holds  for s6 be setHIDDENM2 holds  for s7 be setHIDDENM2 holds  for ns0 be setHIDDENM2 holds  for ns1 be setHIDDENM2 holds  for ns2 be setHIDDENM2 holds  for ns3 be setHIDDENM2 holds  for ns4 be setHIDDENM2 holds  for ns5 be setHIDDENM2 holds  for ns6 be setHIDDENM2 holds  for ns7 be setHIDDENM2 holds  for q1 be setHIDDENM2 holds  for q2 be setHIDDENM2 holds  for q3 be setHIDDENM2 holds  for nq1 be setHIDDENM2 holds  for nq2 be setHIDDENM2 holds  for nq3 be setHIDDENM2 holds  for R be setHIDDENM2 holds ((((((((((((((((((s0 be  non emptyXBOOLE-0V1 iff AND3GATE-1K8(NOT1GATE-1K1 q3,NOT1GATE-1K1 q2,NOT1GATE-1K1 q1) be  non emptyXBOOLE-0V1) & (s1 be  non emptyXBOOLE-0V1 iff AND3GATE-1K8(NOT1GATE-1K1 q3,NOT1GATE-1K1 q2,q1) be  non emptyXBOOLE-0V1)) & (s2 be  non emptyXBOOLE-0V1 iff AND3GATE-1K8(NOT1GATE-1K1 q3,q2,NOT1GATE-1K1 q1) be  non emptyXBOOLE-0V1)) & (s3 be  non emptyXBOOLE-0V1 iff AND3GATE-1K8(NOT1GATE-1K1 q3,q2,q1) be  non emptyXBOOLE-0V1)) & (s4 be  non emptyXBOOLE-0V1 iff AND3GATE-1K8(q3,NOT1GATE-1K1 q2,NOT1GATE-1K1 q1) be  non emptyXBOOLE-0V1)) & (s5 be  non emptyXBOOLE-0V1 iff AND3GATE-1K8(q3,NOT1GATE-1K1 q2,q1) be  non emptyXBOOLE-0V1)) & (s6 be  non emptyXBOOLE-0V1 iff AND3GATE-1K8(q3,q2,NOT1GATE-1K1 q1) be  non emptyXBOOLE-0V1)) & (s7 be  non emptyXBOOLE-0V1 iff AND3GATE-1K8(q3,q2,q1) be  non emptyXBOOLE-0V1)) & (ns0 be  non emptyXBOOLE-0V1 iff AND3GATE-1K8(NOT1GATE-1K1 nq3,NOT1GATE-1K1 nq2,NOT1GATE-1K1 nq1) be  non emptyXBOOLE-0V1)) & (ns1 be  non emptyXBOOLE-0V1 iff AND3GATE-1K8(NOT1GATE-1K1 nq3,NOT1GATE-1K1 nq2,nq1) be  non emptyXBOOLE-0V1)) & (ns2 be  non emptyXBOOLE-0V1 iff AND3GATE-1K8(NOT1GATE-1K1 nq3,nq2,NOT1GATE-1K1 nq1) be  non emptyXBOOLE-0V1)) & (ns3 be  non emptyXBOOLE-0V1 iff AND3GATE-1K8(NOT1GATE-1K1 nq3,nq2,nq1) be  non emptyXBOOLE-0V1)) & (ns4 be  non emptyXBOOLE-0V1 iff AND3GATE-1K8(nq3,NOT1GATE-1K1 nq2,NOT1GATE-1K1 nq1) be  non emptyXBOOLE-0V1)) & (ns5 be  non emptyXBOOLE-0V1 iff AND3GATE-1K8(nq3,NOT1GATE-1K1 nq2,nq1) be  non emptyXBOOLE-0V1)) & (ns6 be  non emptyXBOOLE-0V1 iff AND3GATE-1K8(nq3,nq2,NOT1GATE-1K1 nq1) be  non emptyXBOOLE-0V1)) & (ns7 be  non emptyXBOOLE-0V1 iff AND3GATE-1K8(nq3,nq2,nq1) be  non emptyXBOOLE-0V1)) & (nq1 be  non emptyXBOOLE-0V1 iff AND2GATE-1K2(NOT1GATE-1K1 q1,R) be  non emptyXBOOLE-0V1)) & (nq2 be  non emptyXBOOLE-0V1 iff AND2GATE-1K2(XOR2GATE-1K4(q1,q2),R) be  non emptyXBOOLE-0V1)) & (nq3 be  non emptyXBOOLE-0V1 iff AND2GATE-1K2(OR2GATE-1K3(AND2GATE-1K2(q3,NOT1GATE-1K1 q1),AND2GATE-1K2(q1,XOR2GATE-1K4(q2,q3))),R) be  non emptyXBOOLE-0V1) implies (((((((ns1 be  non emptyXBOOLE-0V1 iff AND2GATE-1K2(s0,R) be  non emptyXBOOLE-0V1) & (ns2 be  non emptyXBOOLE-0V1 iff AND2GATE-1K2(s1,R) be  non emptyXBOOLE-0V1)) & (ns3 be  non emptyXBOOLE-0V1 iff AND2GATE-1K2(s2,R) be  non emptyXBOOLE-0V1)) & (ns4 be  non emptyXBOOLE-0V1 iff AND2GATE-1K2(s3,R) be  non emptyXBOOLE-0V1)) & (ns5 be  non emptyXBOOLE-0V1 iff AND2GATE-1K2(s4,R) be  non emptyXBOOLE-0V1)) & (ns6 be  non emptyXBOOLE-0V1 iff AND2GATE-1K2(s5,R) be  non emptyXBOOLE-0V1)) & (ns7 be  non emptyXBOOLE-0V1 iff AND2GATE-1K2(s6,R) be  non emptyXBOOLE-0V1)) & (ns0 be  non emptyXBOOLE-0V1 iff OR2GATE-1K3(s7,NOT1GATE-1K1 R) be  non emptyXBOOLE-0V1)"
sorry

end

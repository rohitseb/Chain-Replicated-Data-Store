-------------------------------- MODULE test --------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS N, C, STOP, FAILNUM
ASSUME N-FAILNUM>=1/\STOP<5/\/\0<=FAILNUM/\FAILNUM<=2
Nodes == 1..N
Clients == N+1..N+C
Procs == 1..N+C
Configurator == N+C+1

(*
--algorithm test{
    variable FailNum = FAILNUM, step=0, LSTWR=-1,CURRD=-1, lsttmp=-1,WRTFLG=-1,
                msg = [j \in Procs |-> <<>>],
                up = [n \in Nodes |-> TRUE],
                db = [n \in Nodes |-> [ver |-> -1, val |-> -1, cli |-> -1]],
                chain = <<>>;
                
    define
    {     
        
        UpNodes == {i \in Nodes : up[i]=TRUE}
        ChainNode == {chain[i]: i \in 1..Len(chain)}
        ChainNodes == IF (Len(chain)=0) THEN {-1} ELSE ChainNode
        InChain(s) == IF (s \in ChainNodes) THEN TRUE ELSE FALSE \* Doubt??
        FreeUpNodes == {i \in UpNodes: InChain(i)=FALSE /\ up[i]=TRUE}
        GetIndex(s) == CHOOSE i \in 1..Len(chain): chain[i]=s
        GetNext(s) == IF (GetIndex(s)=Len(chain)) THEN -1 ELSE chain[GetIndex(s)+1]
        GetFreeNode == {i \in FreeUpNodes: up[i]=TRUE}
        GetTail == chain[Len(chain)]                                               \* Get the tail of chain
        GetHead == chain[1]
        test(e) == IF (up[e]=TRUE) THEN TRUE ELSE FALSE                                                \* Get the head of chain
    }  
    
    fair process(c \in Clients)
    variable cntr = 0, hver = -1, lastelm = 0, tail=-1, head=-1, initial=0;
    {
        C0:await(Len(chain)>0);
        step:=step+1;
        print <<step,"-b4 read: ", chain>>; 
        CL:while(cntr<=STOP)
        {
            step:=step+1;
            print <<step,"-enter read @",self," with readcmpl=",WRTFLG," :",chain>>;
            CLR: 
                while(WRTFLG#self)
                {
                     if(msg[self]#<<>>)
                     {
                         if(msg[self].val = -1)
                         {
                             hver:=msg[self].ver+1;
                             CURRD:=msg[self].ver||LSTWR:=lsttmp;
                             if(WRTFLG=-1)
                             {
                                 WRTFLG:=self;
                             };
                             print <<step, "-Read Complete">>;
                         }
                     };
                     if(WRTFLG#self)
                     {
                         tail := GetTail;
                         msg[tail]:=[ver |-> -1, val |-> -1, cli |-> self];
                         step:=step+1;
                         print <<step,"-Read request sent at",self," to",tail,": ", chain,msg>>;
                     }
                };
            CLW: 
                while(WRTFLG=self){
                    if(msg[self].val#-1 /\ msg[self].ver=hver)
                    {
                        lsttmp:=msg[self].ver;
                        print <<step, "-Write Complete", db>>;
                        cntr:=cntr+1;
                        WRTFLG:=-1;
\*                        goto C0;
                    };
                    if(WRTFLG=self)
                    {
                    head := GetHead;
\*                    hver:=hver+1;
                    msg[head]:=[ver |-> hver, val|-> cntr, cli |-> self];
                    step:=step+1;
                    print <<step,"-Write request sent at",self," to",head,": ", chain, msg>>;
                        
                    }
              }
        }
    }
    fair process(n \in Nodes)
    variable nextnode=-1,clientid = 0;
    {
        ND:while(TRUE)
        {
            either
            NM:
            { \* react to message
               if(up[self]=TRUE /\ msg[self]#<<>> /\ InChain(self)=TRUE)
               {
                    clientid:=msg[self].cli;
                    step:=step+1;
                    print <<step,"-enter msg request handiler at ",self," :",chain>>;
\*                    NM1:
\*                    {
                        if(msg[self].val=-1 /\ self=GetTail) \* handling Read message request
                        {
                            msg[clientid]:=[ver |-> db[self].ver, val|-> -1, cli |-> clientid]||msg[self]:=<<>>;
\*                            step:=step+1;
                            print <<step,"-Read req reply sent at ",self," :",chain,msg>>;
                            
                        }
                        else if(msg[self].val#-1) \* handling Write message request
                        {
\*                            step:=step+1;
\*                            if(msg[self].ver>db[self].ver) \* writes only if version# of msg > db version#
\*                            {
                                db[self]:=[ver |-> msg[self].ver, val|-> msg[self].val, cli |-> msg[self].cli];
                                print <<step,"-DB write at ",self," :",chain,db>>;
\*                            };
                            if(self=GetTail)        \* check if this is a tail node
                            {
                                msg[clientid]:=[ver |-> db[self].ver, val|-> db[self].val, cli |-> clientid]||msg[self]:=<<>>;
                                print <<step,"-write req reply sent at ",self," :",chain,msg>>;
                            }
                            else                    \* else get the successor
                            {
                                nextnode:= GetNext(self);
                                msg[nextnode]:=msg[self]||msg[self]:=<<>>;
                                print <<step,"-Moving to successor of ",self," at", nextnode," :",chain,msg>>;
                            }
                        };
                        
\*                    };
                    
               } 
            }or
            NDF:
            {
                if(FailNum>0/\up[self]=TRUE) \*Storage node can fail
                {
                   up[self] := FALSE;
                   FailNum := FailNum-1;
                   step:=step+1;
                   print <<step,"-Node Failed at ",self, " :" ,chain>>;
                }
                else if( up[self] = FALSE)  \*Or recover as a new node
               {
                   up[self] := TRUE;
                   msg[self]:= <<>>;
                   FailNum := FailNum+1;  
                   step:=step+1;
                   print <<step,"-Node brought up at ",self, " :" ,chain>>;
                }
             }
        }
    }
    fair process(p=Configurator) \* Maintain the chain
    variable newnode=-1;
    {
        P:while(TRUE)
        {
           P1:
           if(Len(chain)<3) \*Add a new node
           {
                {
                if(FreeUpNodes#{})
                {
                    newnode:=CHOOSE k \in FreeUpNodes: TRUE;                    
                     if(Len(chain)=0)
                        {
                            db[newnode]:=[ver |-> -1, val |-> -1, cli |-> 0];
                            chain:=Append(chain,newnode);
                        }
                        else
                        {
        
                            db[newnode]:=db[chain[Len(chain)]];
                            chain:=Append(chain,newnode);
                        };
                        step:=step+1;
                        print <<step,"-Adding Node: ", chain>>;
                     };
                }
           }
           else
           {
                chain:=SelectSeq(chain, test);
                step:=step+1;
                print <<step,"-Failed Node removed: ", chain>>;
           }
        }
    }
}

*)
\* BEGIN TRANSLATION
VARIABLES FailNum, step, LSTWR, CURRD, lsttmp, WRTFLG, msg, up, db, chain, pc

(* define statement *)
UpNodes == {i \in Nodes : up[i]=TRUE}
ChainNode == {chain[i]: i \in 1..Len(chain)}
ChainNodes == IF (Len(chain)=0) THEN {-1} ELSE ChainNode
InChain(s) == IF (s \in ChainNodes) THEN TRUE ELSE FALSE
FreeUpNodes == {i \in UpNodes: InChain(i)=FALSE /\ up[i]=TRUE}
GetIndex(s) == CHOOSE i \in 1..Len(chain): chain[i]=s
GetNext(s) == IF (GetIndex(s)=Len(chain)) THEN -1 ELSE chain[GetIndex(s)+1]
GetFreeNode == {i \in FreeUpNodes: up[i]=TRUE}
GetTail == chain[Len(chain)]
GetHead == chain[1]
test(e) == IF (up[e]=TRUE) THEN TRUE ELSE FALSE

VARIABLES cntr, hver, lastelm, tail, head, initial, nextnode, clientid, 
          newnode

vars == << FailNum, step, LSTWR, CURRD, lsttmp, WRTFLG, msg, up, db, chain, 
           pc, cntr, hver, lastelm, tail, head, initial, nextnode, clientid, 
           newnode >>

ProcSet == (Clients) \cup (Nodes) \cup {Configurator}

Init == (* Global variables *)
        /\ FailNum = FAILNUM
        /\ step = 0
        /\ LSTWR = -1
        /\ CURRD = -1
        /\ lsttmp = -1
        /\ WRTFLG = -1
        /\ msg = [j \in Procs |-> <<>>]
        /\ up = [n \in Nodes |-> TRUE]
        /\ db = [n \in Nodes |-> [ver |-> -1, val |-> -1, cli |-> -1]]
        /\ chain = <<>>
        (* Process c *)
        /\ cntr = [self \in Clients |-> 0]
        /\ hver = [self \in Clients |-> -1]
        /\ lastelm = [self \in Clients |-> 0]
        /\ tail = [self \in Clients |-> -1]
        /\ head = [self \in Clients |-> -1]
        /\ initial = [self \in Clients |-> 0]
        (* Process n *)
        /\ nextnode = [self \in Nodes |-> -1]
        /\ clientid = [self \in Nodes |-> 0]
        (* Process p *)
        /\ newnode = -1
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "C0"
                                        [] self \in Nodes -> "ND"
                                        [] self = Configurator -> "P"]

C0(self) == /\ pc[self] = "C0"
            /\ (Len(chain)>0)
            /\ step' = step+1
            /\ PrintT(<<step',"-b4 read: ", chain>>)
            /\ pc' = [pc EXCEPT ![self] = "CL"]
            /\ UNCHANGED << FailNum, LSTWR, CURRD, lsttmp, WRTFLG, msg, up, db, 
                            chain, cntr, hver, lastelm, tail, head, initial, 
                            nextnode, clientid, newnode >>

CL(self) == /\ pc[self] = "CL"
            /\ IF cntr[self]<=STOP
                  THEN /\ step' = step+1
                       /\ PrintT(<<step',"-enter read @",self," with readcmpl=",WRTFLG," :",chain>>)
                       /\ pc' = [pc EXCEPT ![self] = "CLR"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ step' = step
            /\ UNCHANGED << FailNum, LSTWR, CURRD, lsttmp, WRTFLG, msg, up, db, 
                            chain, cntr, hver, lastelm, tail, head, initial, 
                            nextnode, clientid, newnode >>

CLR(self) == /\ pc[self] = "CLR"
             /\ IF WRTFLG#self
                   THEN /\ IF msg[self]#<<>>
                              THEN /\ IF msg[self].val = -1
                                         THEN /\ hver' = [hver EXCEPT ![self] = msg[self].ver+1]
                                              /\ /\ CURRD' = msg[self].ver
                                                 /\ LSTWR' = lsttmp
                                              /\ IF WRTFLG=-1
                                                    THEN /\ WRTFLG' = self
                                                    ELSE /\ TRUE
                                                         /\ UNCHANGED WRTFLG
                                              /\ PrintT(<<step, "-Read Complete">>)
                                         ELSE /\ TRUE
                                              /\ UNCHANGED << LSTWR, CURRD, 
                                                              WRTFLG, hver >>
                              ELSE /\ TRUE
                                   /\ UNCHANGED << LSTWR, CURRD, WRTFLG, hver >>
                        /\ IF WRTFLG'#self
                              THEN /\ tail' = [tail EXCEPT ![self] = GetTail]
                                   /\ msg' = [msg EXCEPT ![tail'[self]] = [ver |-> -1, val |-> -1, cli |-> self]]
                                   /\ step' = step+1
                                   /\ PrintT(<<step',"-Read request sent at",self," to",tail'[self],": ", chain,msg'>>)
                              ELSE /\ TRUE
                                   /\ UNCHANGED << step, msg, tail >>
                        /\ pc' = [pc EXCEPT ![self] = "CLR"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "CLW"]
                        /\ UNCHANGED << step, LSTWR, CURRD, WRTFLG, msg, hver, 
                                        tail >>
             /\ UNCHANGED << FailNum, lsttmp, up, db, chain, cntr, lastelm, 
                             head, initial, nextnode, clientid, newnode >>

CLW(self) == /\ pc[self] = "CLW"
             /\ IF WRTFLG=self
                   THEN /\ IF msg[self].val#-1 /\ msg[self].ver=hver[self]
                              THEN /\ lsttmp' = msg[self].ver
                                   /\ PrintT(<<step, "-Write Complete", db>>)
                                   /\ cntr' = [cntr EXCEPT ![self] = cntr[self]+1]
                                   /\ WRTFLG' = -1
                              ELSE /\ TRUE
                                   /\ UNCHANGED << lsttmp, WRTFLG, cntr >>
                        /\ IF WRTFLG'=self
                              THEN /\ head' = [head EXCEPT ![self] = GetHead]
                                   /\ msg' = [msg EXCEPT ![head'[self]] = [ver |-> hver[self], val|-> cntr'[self], cli |-> self]]
                                   /\ step' = step+1
                                   /\ PrintT(<<step',"-Write request sent at",self," to",head'[self],": ", chain, msg'>>)
                              ELSE /\ TRUE
                                   /\ UNCHANGED << step, msg, head >>
                        /\ pc' = [pc EXCEPT ![self] = "CLW"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "CL"]
                        /\ UNCHANGED << step, lsttmp, WRTFLG, msg, cntr, head >>
             /\ UNCHANGED << FailNum, LSTWR, CURRD, up, db, chain, hver, 
                             lastelm, tail, initial, nextnode, clientid, 
                             newnode >>

c(self) == C0(self) \/ CL(self) \/ CLR(self) \/ CLW(self)

ND(self) == /\ pc[self] = "ND"
            /\ \/ /\ pc' = [pc EXCEPT ![self] = "NM"]
               \/ /\ pc' = [pc EXCEPT ![self] = "NDF"]
            /\ UNCHANGED << FailNum, step, LSTWR, CURRD, lsttmp, WRTFLG, msg, 
                            up, db, chain, cntr, hver, lastelm, tail, head, 
                            initial, nextnode, clientid, newnode >>

NM(self) == /\ pc[self] = "NM"
            /\ IF up[self]=TRUE /\ msg[self]#<<>> /\ InChain(self)=TRUE
                  THEN /\ clientid' = [clientid EXCEPT ![self] = msg[self].cli]
                       /\ step' = step+1
                       /\ PrintT(<<step',"-enter msg request handiler at ",self," :",chain>>)
                       /\ IF msg[self].val=-1 /\ self=GetTail
                             THEN /\ msg' = [msg EXCEPT ![clientid'[self]] = [ver |-> db[self].ver, val|-> -1, cli |-> clientid'[self]],
                                                        ![self] = <<>>]
                                  /\ PrintT(<<step',"-Read req reply sent at ",self," :",chain,msg'>>)
                                  /\ UNCHANGED << db, nextnode >>
                             ELSE /\ IF msg[self].val#-1
                                        THEN /\ db' = [db EXCEPT ![self] = [ver |-> msg[self].ver, val|-> msg[self].val, cli |-> msg[self].cli]]
                                             /\ PrintT(<<step',"-DB write at ",self," :",chain,db'>>)
                                             /\ IF self=GetTail
                                                   THEN /\ msg' = [msg EXCEPT ![clientid'[self]] = [ver |-> db'[self].ver, val|-> db'[self].val, cli |-> clientid'[self]],
                                                                              ![self] = <<>>]
                                                        /\ PrintT(<<step',"-write req reply sent at ",self," :",chain,msg'>>)
                                                        /\ UNCHANGED nextnode
                                                   ELSE /\ nextnode' = [nextnode EXCEPT ![self] = GetNext(self)]
                                                        /\ msg' = [msg EXCEPT ![nextnode'[self]] = msg[self],
                                                                              ![self] = <<>>]
                                                        /\ PrintT(<<step',"-Moving to successor of ",self," at", nextnode'[self]," :",chain,msg'>>)
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << msg, db, nextnode >>
                  ELSE /\ TRUE
                       /\ UNCHANGED << step, msg, db, nextnode, clientid >>
            /\ pc' = [pc EXCEPT ![self] = "ND"]
            /\ UNCHANGED << FailNum, LSTWR, CURRD, lsttmp, WRTFLG, up, chain, 
                            cntr, hver, lastelm, tail, head, initial, newnode >>

NDF(self) == /\ pc[self] = "NDF"
             /\ IF FailNum>0/\up[self]=TRUE
                   THEN /\ up' = [up EXCEPT ![self] = FALSE]
                        /\ FailNum' = FailNum-1
                        /\ step' = step+1
                        /\ PrintT(<<step',"-Node Failed at ",self, " :" ,chain>>)
                        /\ msg' = msg
                   ELSE /\ IF up[self] = FALSE
                              THEN /\ up' = [up EXCEPT ![self] = TRUE]
                                   /\ msg' = [msg EXCEPT ![self] = <<>>]
                                   /\ FailNum' = FailNum+1
                                   /\ step' = step+1
                                   /\ PrintT(<<step',"-Node brought up at ",self, " :" ,chain>>)
                              ELSE /\ TRUE
                                   /\ UNCHANGED << FailNum, step, msg, up >>
             /\ pc' = [pc EXCEPT ![self] = "ND"]
             /\ UNCHANGED << LSTWR, CURRD, lsttmp, WRTFLG, db, chain, cntr, 
                             hver, lastelm, tail, head, initial, nextnode, 
                             clientid, newnode >>

n(self) == ND(self) \/ NM(self) \/ NDF(self)

P == /\ pc[Configurator] = "P"
     /\ pc' = [pc EXCEPT ![Configurator] = "P1"]
     /\ UNCHANGED << FailNum, step, LSTWR, CURRD, lsttmp, WRTFLG, msg, up, db, 
                     chain, cntr, hver, lastelm, tail, head, initial, nextnode, 
                     clientid, newnode >>

P1 == /\ pc[Configurator] = "P1"
      /\ IF Len(chain)<3
            THEN /\ IF FreeUpNodes#{}
                       THEN /\ newnode' = (CHOOSE k \in FreeUpNodes: TRUE)
                            /\ IF Len(chain)=0
                                  THEN /\ db' = [db EXCEPT ![newnode'] = [ver |-> -1, val |-> -1, cli |-> 0]]
                                       /\ chain' = Append(chain,newnode')
                                  ELSE /\ db' = [db EXCEPT ![newnode'] = db[chain[Len(chain)]]]
                                       /\ chain' = Append(chain,newnode')
                            /\ step' = step+1
                            /\ PrintT(<<step',"-Adding Node: ", chain'>>)
                       ELSE /\ TRUE
                            /\ UNCHANGED << step, db, chain, newnode >>
            ELSE /\ chain' = SelectSeq(chain, test)
                 /\ step' = step+1
                 /\ PrintT(<<step',"-Failed Node removed: ", chain'>>)
                 /\ UNCHANGED << db, newnode >>
      /\ pc' = [pc EXCEPT ![Configurator] = "P"]
      /\ UNCHANGED << FailNum, LSTWR, CURRD, lsttmp, WRTFLG, msg, up, cntr, 
                      hver, lastelm, tail, head, initial, nextnode, clientid >>

p == P \/ P1

Next == p
           \/ (\E self \in Clients: c(self))
           \/ (\E self \in Nodes: n(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Clients : WF_vars(c(self))
        /\ \A self \in Nodes : WF_vars(n(self))
        /\ WF_vars(p)

\* END TRANSLATION
\*Termination == <> (HVER=STOP)
Invariant1 == LSTWR=CURRD
Invariant2 == \A i \in 1..(Len(chain)-1): db[chain[i]].ver>=db[chain[i+1]].ver

=============================================================================
\* Modification History
\* Last modified Thu Dec 08 20:27:28 EST 2016 by anand
\* Created Sat Dec 03 19:14:19 EST 2016 by anand

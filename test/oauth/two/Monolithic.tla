------------------------------- MODULE Monolithic -------------------------------

(***************************************************************************)
(*                                                                         *)
(* This module specifies a model of the OAuth 2.0 protocol.                *)
(* Informal explanation of the protocol:                                   *) 
(*   https://eskang.github.io/assets/papers/sead20.pdf                     *)
(*                                                                         *)
(***************************************************************************)

EXTENDS Naturals

\* UID: User ID
\* CRED: User credentials (i.e., passwords)
\* AUTHCODE: Authorization codes
\* ACCESSTOKEN: Access tokens
\* SESSION: Session tokens
None == "None"
UID == { "IDAlice", "IDEve" }
Cred == { "CredAlice", "CredEve" }
AuthCode == { "CodeAlice", "CodeEve" }
AccessToken == { "TokenAlice", "TokenEve" }
Session == { "SessionX", "SessionY" }
Proc == { "Alice", "Eve" }
\* AuthCode -> AccessToken
\* Ugly, but it doesn't let me define it using function notation [ a |-> b...]
AS_tokens(x) == 
    IF x = "CodeAlice" THEN "TokenAlice" ELSE "TokenEve"
\* UID -> AuthCode
AS_codes(x) ==
    IF x = "IDAlice" THEN "CodeAlice" ELSE "CodeEve"
\* UID -> Cred
AS_creds(x) == 
    IF x = "IDAlice" THEN "CredAlice" ELSE "CredEve"
\* Proc -> Cred
Proc_cred(x) == 
    IF x = "Alice" THEN "CredAlice" ELSE "CredEve"
    
VARIABLE
    client_sessions, \* UID -> Session
    client_codes,    \* Session -> AuthCode
    client_tokens,   \* Session -> AccessToken
    user_session,    \* Proc -> Session
    knows            \* Proc -> AuthCode \cup Cred  

vars == <<client_sessions, client_codes, client_tokens, user_session, knows>>
    
TypeOK == /\ client_sessions \in SUBSET Session
          /\ client_codes \in [Session -> AuthCode \cup {None} ]
          /\ client_tokens \in [Session -> AccessToken \cup {None} ]
          /\ user_session \in [Proc -> Session \cup {None}]
          /\ knows \in [Proc -> SUBSET (AuthCode \cup Cred \cup Session \cup {None})]  
          
\* Helper functions
Range(f) == {f[x] : x \in DOMAIN f}        
        
\* Actions
Initiate(proc, session) == 
    /\ client_sessions' = client_sessions \cup {session}
    /\ ~(session \in client_sessions)        \* session created must be a new one
    /\ user_session' = [user_session EXCEPT ![proc] = session]
    /\ knows' = [knows EXCEPT ![proc] = knows[proc] \cup {session}] 
    /\ UNCHANGED << client_codes, client_tokens >>

Authorize(proc, uid, cred, code) == 
    /\ AS_creds(uid) = cred     \* correct credential must be provided
    /\ AS_codes(uid) = code     \* return a unique code for the user with "uid"
    \* COMMENT OUT THE LINE BELOW FOR A VIOLATION
    /\ cred \in knows[proc]     \* "proc" must know "cred"
    /\ knows' = [knows EXCEPT ![proc] = knows[proc] \cup {code}]
    /\ UNCHANGED << client_codes, client_tokens, client_sessions, user_session >>

Forward(proc, session, code) ==
    /\ session \in client_sessions
    /\ client_codes' = [client_codes EXCEPT ![session] = code]
    /\ user_session[proc] = session
    /\ code \in knows[proc]
    /\ UNCHANGED << client_tokens, client_sessions, user_session, knows >>
    
GetAccessToken(code, token, s) ==
    /\ AS_tokens(code) = token 
    /\ client_codes[s] = code
    /\ client_tokens' = [client_tokens EXCEPT ![s] = token]
    /\ UNCHANGED << client_codes, client_sessions, user_session, knows >>
  
  
\* Initial condition
Init == /\ client_sessions = {}
        /\ client_codes = [s \in Session |-> None]
        /\ client_tokens = [s \in Session |-> None]
        /\ user_session = [p \in Proc |-> None]  
        /\ knows = [p \in Proc |-> {Proc_cred(p)}]
    
\* Transition relation                  
Next == 
    \/ \E p \in Proc : \E s \in Session : Initiate(p, s)
    \/ \E p \in Proc : \E u \in UID : \E cr \in Cred : \E co \in AuthCode : Authorize(p, u, cr, co)    
    \/ \E p \in Proc : \E s \in Session : \E c \in AuthCode : Forward(p, s, c)
    \/ \E c \in AuthCode : \E t \in AccessToken : \E s \in Session : GetAccessToken(c, t, s)

Spec == Init /\ [][Next]_vars

SessionIntegrity ==
    \A s \in Session : (client_tokens[s] = "TokenAlice") => ~(user_session["Eve"] = s)

=============================================================================
\* Modification History
\* Last modified Sun Apr 30 20:56:24 EDT 2023 by eunsukkang
\* Created Fri Apr 28 21:00:26 EDT 2023 by eunsukkang


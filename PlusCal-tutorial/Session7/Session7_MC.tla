---- MODULE Session7_MC ----
EXTENDS Session7

AddCorrect == (pc["ProcA"] = "Done") /\ (pc["ProcB"] = "Done") => (x = 2)

====
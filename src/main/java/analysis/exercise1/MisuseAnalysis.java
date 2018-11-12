package analysis.exercise1;

import analysis.AbstractAnalysis;
import analysis.VulnerabilityReporter;
import soot.Body;
import soot.SootClass;
import soot.SootMethodRef;
import soot.Unit;
import soot.Value;
import soot.jimple.InvokeExpr;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.internal.JAssignStmt;

public class MisuseAnalysis extends AbstractAnalysis{
	public MisuseAnalysis(Body body, VulnerabilityReporter reporter) {
		super(body, reporter);
	}
	
	@Override
	protected void flowThrough(Unit unit) {
		if (unit instanceof JAssignStmt) {
			Stmt stmt = (Stmt) unit;
			if (stmt.containsInvokeExpr()) {
				InvokeExpr exp = ((JAssignStmt) unit).getInvokeExpr();
				
				if (exp instanceof StaticInvokeExpr) {
					SootMethodRef method = exp.getMethodRef();
					if (method.isStatic() && method.getSubSignature().toString()
							.equals("javax.crypto.Cipher getInstance(java.lang.String)")) {
						/*
						 * Question: is it better to use this method?
						 */
						
						
//						if (exp.getArgCount() == 1) {
//							Value arg = exp.getArg(0);
//							if (arg instanceof StringConstant) {
//								if (((StringConstant) arg).value.equals("AES")) {
//									if (!arg.toString().equals("\"AES/GCM/PKCS5Padding\"")) {
//										this.reporter.reportVulnerability(method.getSignature(), unit);
//									}
//								}
//							}
//						}
					}
					if (method.isStatic()) {
						if (method.name().equals("getInstance")) {
							SootClass decClass = method.declaringClass();
							if (decClass.getName().equals("javax.crypto.Cipher")
									&& method.returnType().toString().equals("javax.crypto.Cipher")) {
								if (exp.getArgCount() == 1) {
									Value arg = exp.getArg(0);
									if (arg instanceof StringConstant) {
										if (((StringConstant) arg).value.equals("AES")) {
											if (!arg.toString().equals("\"AES/GCM/PKCS5Padding\"")) {
												this.reporter.reportVulnerability(method.getSignature(), unit);
											}
										}
									}
								}
							}
						}
					}
				}
			}

		}
	}
}

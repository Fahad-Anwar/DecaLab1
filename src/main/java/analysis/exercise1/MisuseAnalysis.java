package analysis.exercise1;

import analysis.AbstractAnalysis;
import analysis.VulnerabilityReporter;
import soot.Body;
import soot.Unit;
import soot.SootMethodRef;
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
				InvokeExpr invokeExpr = ((JAssignStmt) unit).getInvokeExpr();
				if (invokeExpr instanceof StaticInvokeExpr) {
					SootMethodRef sootMethodRef = invokeExpr.getMethodRef();
					if (sootMethodRef.isStatic() && sootMethodRef.getSubSignature().toString()
							.equals("javax.crypto.Cipher getInstance(java.lang.String)")) {
						if (invokeExpr.getArgCount() == 1) {
							Value arg = invokeExpr.getArg(0);
							if (arg instanceof StringConstant) {
								if (((StringConstant) arg).value.equals("AES")
										|| !((StringConstant) arg).value.equals("AES/GCM/PKCS5Padding")) {
									this.reporter.reportVulnerability(this.method.toString(), unit);
								}
							}
						}
					}
					/*
					 * Question: is it better to use this soloution instead of above?
					 */
//					if (method.isStatic() && method.name().equals("getInstance")) {
//						SootClass decClass = method.declaringClass();
//						if (decClass.getName().equals("javax.crypto.Cipher")
//								&& method.returnType().toString().equals("javax.crypto.Cipher")) {
//							if (exp.getArgCount() == 1) {
//								Value arg = exp.getArg(0);
//								if (arg instanceof StringConstant) {
//									if (((StringConstant) arg).value.equals("AES")
//											|| !((StringConstant) arg).value.equals("AES/GCM/PKCS5Padding")) {
//										this.reporter.reportVulnerability(this.method.toString(), unit);
//									}
//								}
//							}
//						}
//					}
				}
			}
		}
	}
}

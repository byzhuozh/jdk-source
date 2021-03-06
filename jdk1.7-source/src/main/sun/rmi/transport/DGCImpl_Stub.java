// Stub class generated by rmic, do not edit.
// Contents subject to change without notice.

package sun.rmi.transport;

public final class DGCImpl_Stub
    extends java.rmi.server.RemoteStub
    implements java.rmi.dgc.DGC
{
    private static final java.rmi.server.Operation[] operations = {
	new java.rmi.server.Operation("void clean(java.rmi.server.ObjID[], long, java.rmi.dgc.VMID, boolean)"),
	new java.rmi.server.Operation("java.rmi.dgc.Lease dirty(java.rmi.server.ObjID[], long, java.rmi.dgc.Lease)")
    };
    
    private static final long interfaceHash = -669196253586618813L;
    
    // constructors
    public DGCImpl_Stub() {
	super();
    }
    public DGCImpl_Stub(java.rmi.server.RemoteRef ref) {
	super(ref);
    }
    
    // methods from remote interfaces
    
    // implementation of clean(ObjID[], long, VMID, boolean)
    public void clean(java.rmi.server.ObjID[] $param_arrayOf_ObjID_1, long $param_long_2, java.rmi.dgc.VMID $param_VMID_3, boolean $param_boolean_4)
	throws java.rmi.RemoteException
    {
	try {
	    java.rmi.server.RemoteCall call = ref.newCall((java.rmi.server.RemoteObject) this, operations, 0, interfaceHash);
	    try {
		java.io.ObjectOutput out = call.getOutputStream();
		out.writeObject($param_arrayOf_ObjID_1);
		out.writeLong($param_long_2);
		out.writeObject($param_VMID_3);
		out.writeBoolean($param_boolean_4);
	    } catch (java.io.IOException e) {
		throw new java.rmi.MarshalException("error marshalling arguments", e);
	    }
	    ref.invoke(call);
	    ref.done(call);
	} catch (java.lang.RuntimeException e) {
	    throw e;
	} catch (java.rmi.RemoteException e) {
	    throw e;
	} catch (java.lang.Exception e) {
	    throw new java.rmi.UnexpectedException("undeclared checked exception", e);
	}
    }
    
    // implementation of dirty(ObjID[], long, Lease)
    public java.rmi.dgc.Lease dirty(java.rmi.server.ObjID[] $param_arrayOf_ObjID_1, long $param_long_2, java.rmi.dgc.Lease $param_Lease_3)
	throws java.rmi.RemoteException
    {
	try {
	    java.rmi.server.RemoteCall call = ref.newCall((java.rmi.server.RemoteObject) this, operations, 1, interfaceHash);
	    try {
		java.io.ObjectOutput out = call.getOutputStream();
		out.writeObject($param_arrayOf_ObjID_1);
		out.writeLong($param_long_2);
		out.writeObject($param_Lease_3);
	    } catch (java.io.IOException e) {
		throw new java.rmi.MarshalException("error marshalling arguments", e);
	    }
	    ref.invoke(call);
	    java.rmi.dgc.Lease $result;
	    try {
		java.io.ObjectInput in = call.getInputStream();
		$result = (java.rmi.dgc.Lease) in.readObject();
	    } catch (java.io.IOException e) {
		throw new java.rmi.UnmarshalException("error unmarshalling return", e);
	    } catch (java.lang.ClassNotFoundException e) {
		throw new java.rmi.UnmarshalException("error unmarshalling return", e);
	    } finally {
		ref.done(call);
	    }
	    return $result;
	} catch (java.lang.RuntimeException e) {
	    throw e;
	} catch (java.rmi.RemoteException e) {
	    throw e;
	} catch (java.lang.Exception e) {
	    throw new java.rmi.UnexpectedException("undeclared checked exception", e);
	}
    }
}

/*
 * ORACLE PROPRIETARY/CONFIDENTIAL. Use is subject to license terms.
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 */

/*
 *
 *  (C) Copyright IBM Corp. 1999 All Rights Reserved.
 *  Copyright 1997 The Open Group Research Institute.  All rights reserved.
 */

package sun.security.krb5.internal;

import sun.security.krb5.*;
import sun.security.util.*;
import java.io.IOException;

public class ASReq extends KDCReq {

    public ASReq(PAData[] new_pAData, KDCReqBody new_reqBody) throws IOException {
        super(new_pAData, new_reqBody, Krb5.KRB_AS_REQ);
    }

    public ASReq(byte[] data) throws Asn1Exception, KrbException, IOException {
        init(new DerValue(data));
    }

    public ASReq(DerValue encoding) throws Asn1Exception, KrbException, IOException {
        init(encoding);
    }

    private void init(DerValue encoding) throws Asn1Exception, IOException, KrbException {
        super.init(encoding, Krb5.KRB_AS_REQ);
    }
}

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

import sun.security.krb5.PrincipalName;
import sun.security.krb5.Realm;
import sun.security.krb5.RealmException;
import sun.security.krb5.EncryptedData;
import sun.security.krb5.Asn1Exception;
import sun.security.util.*;
import java.io.IOException;

public class TGSRep extends KDCRep {

    public TGSRep(
                  PAData[] new_pAData,
                  Realm new_crealm,
                  PrincipalName new_cname,
                  Ticket new_ticket,
                  EncryptedData new_encPart
                      ) throws IOException {
        super(new_pAData, new_crealm, new_cname, new_ticket,
              new_encPart, Krb5.KRB_TGS_REP);
    }

    public TGSRep(byte[] data) throws Asn1Exception,
    RealmException, KrbApErrException, IOException {
        init(new DerValue(data));
    }

    public TGSRep(DerValue encoding) throws Asn1Exception,
    RealmException, KrbApErrException, IOException {
        init(encoding);
    }

    private void init(DerValue encoding) throws Asn1Exception,
    RealmException, KrbApErrException, IOException {
        init(encoding, Krb5.KRB_TGS_REP);
    }

}

/*
 * Copyright (c) 2006, 2010, Oracle and/or its affiliates. All rights reserved.
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

package sun.java2d.cmm;

import java.awt.color.ColorSpace;
import java.awt.color.ICC_Profile;
import java.awt.color.CMMException;
import java.awt.image.BufferedImage;
import java.awt.image.Raster;
import java.awt.image.WritableRaster;
import java.security.AccessController;
import java.security.PrivilegedAction;
import sun.security.action.GetPropertyAction;
import java.util.ServiceLoader;

public class CMSManager {
    public static ColorSpace GRAYspace;       // These two fields allow access
    public static ColorSpace LINEAR_RGBspace; // to java.awt.color.ColorSpace
                                              // private fields from other
                                              // packages.  The fields are set
                                              // by java.awt.color.ColorSpace
                                              // and read by
                                              // java.awt.image.ColorModel.

    private static PCMM cmmImpl = null;

    public static synchronized PCMM getModule() {
        if (cmmImpl != null) {
            return cmmImpl;
        }

        cmmImpl = (PCMM)AccessController.doPrivileged(new PrivilegedAction() {
            public Object run() {
                String cmmClass = System.getProperty(
                    "sun.java2d.cmm", "sun.java2d.cmm.kcms.CMM");

                ServiceLoader<PCMM> cmmLoader
                    = ServiceLoader.loadInstalled(PCMM.class);

                PCMM service = null;

                for (PCMM cmm : cmmLoader) {
                    service = cmm;
                    if (cmm.getClass().getName().equals(cmmClass)) {
                        break;
                    }
                }
                return service;
            }
        });

        if (cmmImpl == null) {
            throw new CMMException("Cannot initialize Color Management System."+
                                   "No CM module found");
        }

        GetPropertyAction gpa = new GetPropertyAction("sun.java2d.cmm.trace");
        String cmmTrace = (String)AccessController.doPrivileged(gpa);
        if (cmmTrace != null) {
            cmmImpl = new CMMTracer(cmmImpl);
        }

        return cmmImpl;
    }

    /* CMM trace routines */

    public static class CMMTracer implements PCMM {
        PCMM tcmm;
        String cName ;

        public CMMTracer(PCMM tcmm) {
            this.tcmm = tcmm;
            cName = tcmm.getClass().getName();
        }

        public long loadProfile(byte[] data) {
            System.err.print(cName + ".loadProfile");
            long profileID = tcmm.loadProfile(data);
            System.err.printf("(ID=%x)\n", profileID);
            return profileID;
        }

        public void freeProfile(long profileID) {
            System.err.printf(cName + ".freeProfile(ID=%x)\n", profileID);
            tcmm.freeProfile(profileID);
        }

        public int getProfileSize(long profileID) {
            System.err.print(cName + ".getProfileSize(ID=" + profileID + ")");
            int size = tcmm.getProfileSize(profileID);
            System.err.println("=" + size);
            return size;
        }

        public void getProfileData(long profileID, byte[] data) {
            System.err.print(cName + ".getProfileData(ID=" + profileID + ") ");
            System.err.println("requested " + data.length + " byte(s)");
            tcmm.getProfileData(profileID, data);
        }

        public int getTagSize(long profileID, int tagSignature) {
            System.err.printf(cName + ".getTagSize(ID=%x, TagSig=%s)",
                              profileID, signatureToString(tagSignature));
            int size = tcmm.getTagSize(profileID, tagSignature);
            System.err.println("=" + size);
            return size;
        }

        public void getTagData(long profileID, int tagSignature,
                               byte[] data) {
            System.err.printf(cName + ".getTagData(ID=%x, TagSig=%s)",
                              profileID, signatureToString(tagSignature));
            System.err.println(" requested " + data.length + " byte(s)");
            tcmm.getTagData(profileID, tagSignature, data);
        }

        public void setTagData(long profileID, int tagSignature,
                               byte[] data) {
            System.err.print(cName + ".setTagData(ID=" + profileID +
                             ", TagSig=" + tagSignature + ")");
            System.err.println(" sending " + data.length + " byte(s)");
            tcmm.setTagData(profileID, tagSignature, data);
        }

        /* methods for creating ColorTransforms */
        public ColorTransform createTransform(ICC_Profile profile,
                                              int renderType,
                                              int transformType) {
            System.err.println(cName + ".createTransform(ICC_Profile,int,int)");
            return tcmm.createTransform(profile, renderType, transformType);
        }

        public ColorTransform createTransform(ColorTransform[] transforms) {
            System.err.println(cName + ".createTransform(ColorTransform[])");
            return tcmm.createTransform(transforms);
        }

        private static String signatureToString(int sig) {
            return String.format("%c%c%c%c",
                                 (char)(0xff & (sig >> 24)),
                                 (char)(0xff & (sig >> 16)),
                                 (char)(0xff & (sig >>  8)),
                                 (char)(0xff & (sig      )));
        }
    }
}
